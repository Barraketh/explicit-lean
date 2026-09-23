#!/usr/bin/env python3
"""Render a `simp-trace-v1` trace as `explicit_rw` source text.

The source of truth is `tracking/SIMP-TRACE-SPEC.md` together with the step
grammar documented in T2's `ExplicitLean/ExplicitRw/Tactic.lean`. Every token
this module emits comes from a spec field; nothing is tuned per trace, and
nothing papers over a recorder that emits something the spec does not define.

A render either succeeds, or raises `RenderError` naming the field and reason.
Callers turn that into a `render_failed:<reason>` site status; they must never
silently drop a step.

Rendering rules, in one place:

* `rw`     -> `[← ]lean_term(<term>) at [pos][ with [side, ...]]` for
              source-backed terms, where `<term>` is the authenticated source term; legacy
              names and their parenthesized arguments retain their spelling.
* `unfold` -> `unfold <name> at [pos]`
* `beta`/`eta`/`proj`/`iota` -> `<kind> at [pos]`; unnamed `zeta` uses the
  same form, while named `zeta` (a local-definition unfold) uses
  `change <after> at [pos]`
* `change` -> `change <to> at [pos]`
* `eq`     -> `eq (<lhs> = <rhs>) by <by> at [pos]`
* `congr`  -> `congr <arg> [<nested steps>] at [pos]`
* `transport` -> `transport forall <handle> [<domain steps>] body
                 [<body steps>] at [pos]`
* `intro_ctx` -> `intro_ctx <handle> domain at <domain-pos> deps [..]
                 scope <scope> enter at <enter> exit at <exit>
                 with [<nested steps>] at <pos>`

Closes map through one table: `rfl`/`decide`/`omega`/`nofun` render as
themselves, `true_intro` as `close [True.intro]`, `assumption:<n>` as
`close [<n>]`, `absurd:<h>` as `close [<h>.elim]`. Anything else, including every
`unresolved:<reason>`, is not a close this renderer invents a spelling for.
"""

from __future__ import annotations

import re
from typing import Any

# Spec step kinds.
REDUCTION_KINDS = ("beta", "eta", "proj", "zeta", "iota")
KNOWN_KINDS = ("rw", "unfold", "change", "eq", "congr", "transport", "intro_ctx") + REDUCTION_KINDS

# A name the whitelisted term grammar admits as a bare identifier: dotted
# components of identifier characters, optionally `@`-prefixed. Lean identifiers
# admit a wide unicode range, but two classes must never be spliced:
# inaccessible display names (`h✝`), which do not lex at all, and hygienic
# internal names (`h._@.Mod.123._hygCtx._hyg.71`), which do not resolve.
_IDENT_CHAR = r"[^\s(){}\[\],;:✝]"
IDENT_RE = re.compile(rf"@?{_IDENT_CHAR}+")
HYGIENIC_RE = re.compile(r"\._@\.|\._hyg")


class RenderError(Exception):
    """A trace field the renderer refuses to translate.

    `reason` is a short stable tag used as the site status; `detail` is the
    one-line human explanation, and `side` is the task the field belongs to
    (`t1` for a malformed or missing trace field, `t2` for a construct the
    tactic has no syntax for, `harness` for a renderer bug).
    """

    def __init__(self, reason: str, detail: str, side: str = "t1") -> None:
        super().__init__(f"{reason}: {detail}")
        self.reason = reason
        self.detail = detail
        self.side = side


def check_name(name: Any, what: str) -> str:
    """Validate a spec field the spec calls a *name* before splicing it.

    The spec says `rw.name` and `unfold.name` are "<lemma or hyp name>", and
    `local` exists so a generator can tell a hypothesis from a constant. A field
    holding written syntax instead (`if_neg fun h ↦ hb ⟨a, h⟩`, `heq_comm
    (a := a)`) is a recorder defect: it is not in T2's whitelisted grammar, and
    concatenating it with `args` produces spurious arguments. Refuse it here so
    the site is reported and attributed, never mis-rendered.
    """
    if not isinstance(name, str) or not name:
        raise RenderError("bad_name", f"{what} is not a non-empty string: {name!r}")
    if "✝" in name:
        raise RenderError(
            "inaccessible_name",
            f"{what} {name!r} is an inaccessible display name, which does not lex",
        )
    if HYGIENIC_RE.search(name):
        raise RenderError(
            "hygienic_name",
            f"{what} {name!r} is a raw hygienic name, not a user name",
        )
    if not IDENT_RE.fullmatch(name):
        raise RenderError(
            "name_is_syntax",
            f"{what} {name!r} is written syntax, not a name (spec: '<lemma or hyp name>')",
        )
    return name


def check_term(text: Any, what: str) -> str:
    """Validate a spec field a replayer splices as a *term*.

    `change.to` and `eq.lhs`/`eq.rhs` are written in the ordinary
    `lean_term(...)` form admitted by ExplicitRw. `args` are separately
    parenthesized as application arguments. Two recorder artifacts
    are still rejected: the elision marker `⋯` (which is pretty-printer output,
    not a term) and the stale `pp.all` `nat_lit` annotation. Embedded newlines
    are refused because this renderer emits one-line step syntax.
    """
    if not isinstance(text, str) or not text.strip():
        raise RenderError("bad_term", f"{what} is not a non-empty string: {text!r}")
    if "⋯" in text:
        raise RenderError("elided_term", f"{what} contains the elision marker ⋯: {text!r}")
    if "\n" in text:
        raise RenderError("multiline_term", f"{what} contains a newline: {text!r}")
    # Fresh recorder output uses ordinary Lean surface syntax and explicitly
    # disables universe printing.  Do not normalize the authenticated text:
    # even punctuation that resembles a pp.all annotation may occur inside a
    # string literal and must be preserved byte-for-byte.  Keep stale
    # `nat_lit` output rejected; it is an internal constructor, not a term.
    if re.search(r"(?<![\w.])nat_lit\b", text):
        raise RenderError(
            "pp_all_term",
            f"{what} is pp.all output (nat_lit): {text!r}",
        )
    if "✝" in text:
        raise RenderError(
            "inaccessible_name", f"{what} splices an inaccessible name: {text!r}"
        )
    # These are simp-argument/configuration spellings, not Lean terms. The
    # authenticated source span may contain arbitrary ordinary term syntax,
    # including named arguments and record updates; Lean's parser, rather than
    # a punctuation check here, distinguishes those forms.
    checked = text.strip()
    if checked in ("*", "_") or re.fullmatch(r"-[^\s]+", checked):
        raise RenderError(
            "unparseable_source_argument",
            f"{what} is simp syntax rather than an explicit_rw term: {text!r}",
        )
    if "by " in text or checked.endswith(" by"):
        raise RenderError("term_has_by", f"{what} contains a `by` block: {text!r}")
    return text


def render_pos(pos: Any) -> str:
    """`[0, 1, 1]` -> `at [0, 1, 1]`; `[]` -> `at []`."""
    if not isinstance(pos, list) or not all(
        isinstance(i, int) and i >= 0 for i in pos
    ):
        raise RenderError("bad_pos", f"pos is not a list of child indices: {pos!r}")
    return "at [" + ", ".join(str(i) for i in pos) + "]"


def atomize(term: str) -> str:
    """Parenthesise a compound term so application binds as intended."""
    term = term.strip()
    if not term:
        raise RenderError("bad_term", "empty term")
    if IDENT_RE.fullmatch(term):
        return term
    if term.startswith("(") and term.endswith(")"):
        depth = 0
        for i, ch in enumerate(term):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(term) - 1:
                    break
        else:
            return term
    return f"({term})"


def lean_term(term: str) -> str:
    """Delimit an ordinary Lean term in the ExplicitRw DSL."""
    if not term.strip():
        raise RenderError("bad_term", "empty term")
    return f"lean_term({term})"


def render_close(close: Any, introduced: dict[str, int] | None = None) -> str:
    """Map a spec `close` object onto a T2 side-proof / closer.

    The mapping is exactly the one T2 documents: the tactic offers no `trivial`
    and no bare `assumption`, because both search where the spec recorded an
    exact choice.
    """
    if not isinstance(close, dict) or "by" not in close:
        raise RenderError("bad_close", f"close is not an object with `by`: {close!r}")
    by = close["by"]
    if not isinstance(by, str):
        raise RenderError("bad_close", f"close.by is not a string: {by!r}")
    def exact(term: str) -> str:
        return f"close [{term}]"

    if by in ("rfl", "decide", "omega", "nofun"):
        return by
    if by == "true_intro":
        return exact("True.intro")
    if by.startswith("assumption:"):
        name = by[len("assumption:") :]
        if introduced and name in introduced:
            return exact(f"introduced_ref {introduced[name]}")
        return exact(check_name(name, "close.by assumption"))
    if by.startswith("absurd:"):
        name = by[len("absurd:") :]
        if introduced and name in introduced:
            return exact(f"(introduced_ref {introduced[name]}).elim")
        return exact(check_name(name, "close.by absurd") + ".elim")
    if by.startswith("unresolved:"):
        raise RenderError("unresolved_close", f"close.by is {by!r}", side="t1")
    raise RenderError("unknown_close", f"close.by {by!r} is not a spec close form")


DERIVATION_SOURCES = {"simp-argument", "local-evidence", "operational", "congr"}
DERIVATION_CLASSIFICATIONS = {"matched", "instance", "discharge", "congruence"}
DERIVATION_OPERATIONS = {
    "direct_eq",
    "iff_propext",
    "prop_to_true",
    "not_to_false",
    "conjunction_left",
    "conjunction_right",
    "conjunction_projection",
    "reverse",
    "congruence",
}


def source_argument(source_text: Any, source_args: Any, arg_id: Any) -> tuple[str, str]:
    """Read one source argument by T22's direct identity and source span.

    The producer records Unicode-scalar ``startChar``/``endChar`` ranges in the
    module source.  The renderer does not parse ``callText`` or infer an
    argument ordinal: it selects the recorded ``argId`` and slices that exact
    span.  ``direction`` is metadata, not reconstructed from theorem names.
    """
    if not isinstance(source_text, str):
        raise RenderError("missing_source_text", "source argument needs the original module source")
    if not isinstance(source_args, list):
        raise RenderError("missing_source_args", "trace site has no T22 sourceArgs array")
    if not isinstance(arg_id, int) or isinstance(arg_id, bool) or arg_id < 0:
        raise RenderError("bad_source_arg", f"derivation.argId is invalid: {arg_id!r}")
    matches = [entry for entry in source_args
               if isinstance(entry, dict) and entry.get("argId") == arg_id]
    if len(matches) != 1:
        raise RenderError("source_arg_identity", f"T22 sourceArgs has {len(matches)} entries for argId {arg_id}")
    entry = matches[0]
    start, end = entry.get("startChar"), entry.get("endChar")
    direction = entry.get("direction")
    if (not isinstance(start, int) or isinstance(start, bool)
            or not isinstance(end, int) or isinstance(end, bool)
            or start < 0 or end < start or end > len(source_text)):
        raise RenderError("bad_source_span", f"sourceArgs[{arg_id}] has invalid span {start!r}:{end!r}")
    if direction not in ("fwd", "rev"):
        raise RenderError("bad_source_direction", f"sourceArgs[{arg_id}].direction is {direction!r}")
    term = source_text[start:end].strip()
    # Source syntax accepts Unicode `↦`, while ExplicitRw's term grammar
    # admits the equivalent ASCII lambda arrow. This is a syntax-only
    # normalization of the authenticated direct span, not reconstruction.
    term = term.replace("↦", "=>")
    if direction == "rev":
        if term.startswith("←"):
            term = term[1:].lstrip()
        elif term.startswith("<-"):
            term = term[2:].lstrip()
        else:
            raise RenderError("source_direction_mismatch", f"sourceArgs[{arg_id}] is rev but its span has no reverse marker")
    elif term.startswith("←") or term.startswith("<-"):
        raise RenderError("source_direction_mismatch", f"sourceArgs[{arg_id}] is fwd but its span has a reverse marker")
    return term, direction


def _validate_derivation(step: dict, derivation: Any, source_text: Any,
                         source_args: Any,
                         operational: bool,
                         depth: int = 0) -> dict:
    """Validate the term-free T16 contract before rendering a theorem step."""
    if not isinstance(derivation, dict):
        raise RenderError("bad_derivation", "rw.derivation is not an object", side="t1")
    if not isinstance(derivation.get("origin"), str) or not derivation["origin"]:
        raise RenderError("bad_derivation", "derivation.origin is not a non-empty string", side="t1")
    source = derivation.get("source")
    if source is not None and source not in DERIVATION_SOURCES:
        raise RenderError("bad_derivation_source", f"derivation.source {source!r} is not recognised", side="t1")
    derivation_direction = derivation.get("direction")
    if derivation_direction is not None and derivation_direction not in ("fwd", "rev"):
        raise RenderError("bad_derivation_direction", f"derivation.direction is {derivation_direction!r}", side="t1")
    arg_id = derivation.get("argId")
    if source != "simp-argument" and arg_id is not None:
        raise RenderError("bad_source_arg", "argId is present without source=simp-argument", side="t1")
    preprocess = derivation.get("preprocess", [])
    if not isinstance(preprocess, list) or not all(isinstance(op, str) for op in preprocess):
        raise RenderError("bad_preprocess", "derivation.preprocess is not an array of strings", side="t1")
    if any(op not in DERIVATION_OPERATIONS for op in preprocess):
        unknown = next(op for op in preprocess if op not in DERIVATION_OPERATIONS)
        raise RenderError("unknown_preprocess", f"unknown derivation operation {unknown!r}", side="t1")
    reverse_count = preprocess.count("reverse")
    non_reverse = [op for op in preprocess if op != "reverse"]
    if source == "operational":
        # Simproc provenance is carried by the nested `simproc` object; it has
        # no theorem preprocessing operation to replay.
        if preprocess:
            raise RenderError("bad_preprocess", "operational derivation must not carry theorem preprocessing", side="t1")
    elif reverse_count > 1 or len(non_reverse) != 1:
        raise RenderError("bad_preprocess", "derivation needs exactly one non-reverse operation", side="t1")

    extra = derivation.get("extraArgs", 0)
    if not isinstance(extra, int) or isinstance(extra, bool) or extra < 0:
        raise RenderError("bad_extra_args", f"derivation.extraArgs is invalid: {extra!r}", side="t1")
    pos = step.get("pos")
    redex = derivation.get("redex")
    if not isinstance(redex, list) or not all(isinstance(i, int) and not isinstance(i, bool) and i >= 0 for i in redex):
        raise RenderError("bad_redex", f"derivation.redex is invalid: {redex!r}", side="t1")
    # T16 records the already-adjusted application position in `redex`; the
    # separate extraArgs count is provenance only. Proposition derivations
    # retain the theorem's empty application redex while the enclosing step
    # position selects the proposition, so T17 consumes that pair directly.
    # Never append a function spine here (Option.orElse and prefix-function
    # rules use the recorded position).
    prop_redex = any(op in preprocess for op in ("prop_to_true", "not_to_false"))
    if (not isinstance(pos, list)
            or (depth == 0 and redex != pos
                and not (prop_redex and redex == []))):
        raise RenderError("redex_mismatch", "derivation.redex does not match the step position", side="t1")

    binders = derivation.get("binders", [])
    if not isinstance(binders, list):
        raise RenderError("bad_binders", "derivation.binders is not an array", side="t1")
    binder_ids: list[int] = []
    classifications: list[str] = []
    for binder in binders:
        if not isinstance(binder, dict):
            raise RenderError("bad_binder", "derivation binder is not an object", side="t1")
        ident = binder.get("id")
        classification = binder.get("classification")
        if not isinstance(ident, int) or isinstance(ident, bool) or ident < 0 or ident >= len(binders):
            raise RenderError("binder_out_of_range", f"binder id {ident!r} is outside the binder array", side="t1")
        if ident in binder_ids:
            raise RenderError("duplicate_binder", f"binder id {ident} occurs more than once", side="t1")
        if classification not in DERIVATION_CLASSIFICATIONS:
            raise RenderError("bad_binder_classification", f"binder classification {classification!r} is not recognised", side="t1")
        binder_ids.append(ident)
        classifications.append(classification)

    discharge = derivation.get("discharge", [])
    if not isinstance(discharge, list):
        raise RenderError("bad_discharge", "derivation.discharge is not an array", side="t1")
    discharge_ids = [ident for ident, cls in zip(binder_ids, classifications) if cls == "discharge"]
    observed_discharge: list[int] = []
    for item in discharge:
        if not isinstance(item, dict):
            raise RenderError("bad_discharge", "discharge entry is not an object", side="t1")
        ident = item.get("binder")
        if ident not in binder_ids or ident in observed_discharge or not isinstance(item.get("provenance"), str):
            raise RenderError("bad_discharge", f"discharge binder {ident!r} is invalid", side="t1")
        observed_discharge.append(ident)
    if observed_discharge != discharge_ids:
        raise RenderError("discharge_mismatch", "discharge entries do not match discharge binders in order", side="t1")

    side = step.get("side", [])
    if not isinstance(side, list):
        raise RenderError("side_mismatch", "side traces are not an array", side="t1")
    congruence_ids = [ident for ident, cls in zip(binder_ids, classifications)
                      if cls == "congruence"]
    expected_side_count = (1 if source == "operational"
                           else len(congruence_ids) if source == "congr"
                           else len(discharge_ids))
    if len(side) != expected_side_count:
        raise RenderError("side_mismatch", "side traces do not pair with recorded binders", side="t1")
    if source == "operational":
        simproc = derivation.get("simproc")
        if not isinstance(simproc, dict):
            raise RenderError("bad_simproc", "operational derivation has no simproc record", side="t1")
        sim_source = simproc.get("source")
        if sim_source not in ("reduceIte", "reduceDIte"):
            raise RenderError("bad_simproc", f"simproc.source is {sim_source!r}", side="t1")
        if simproc.get("redex") != pos or simproc.get("extraArgs") != extra:
            raise RenderError("simproc_mismatch", "simproc redex/extraArgs disagree with the rule derivation", side="t1")
        if simproc.get("branch") not in ("true", "false"):
            raise RenderError("bad_simproc", f"simproc.branch is {simproc.get('branch')!r}", side="t1")
        expected_constructor = ("ite_cond_eq_" if sim_source == "reduceIte"
                                else "dite_cond_eq_") + simproc["branch"]
        if simproc.get("constructor") != expected_constructor:
            raise RenderError("bad_simproc", "simproc.constructor disagrees with source/branch", side="t1")
    if source == "simp-argument":
        _, source_direction = source_argument(source_text, source_args, arg_id)
        if derivation_direction is not None and derivation_direction != source_direction:
            raise RenderError("direction_mismatch", "derivation.direction disagrees with T22 sourceArgs.direction", side="t1")
    elif source == "local-evidence":
        local = step.get("local")
        if not isinstance(local, dict) or not isinstance(step.get("name"), str):
            raise RenderError("bad_local_evidence", "local-evidence lacks its stable local reference", side="t1")
    prop = step.get("prop")
    projected_prop = any(op in preprocess for op in
                         ("conjunction_left", "conjunction_right",
                          "conjunction_projection"))
    mapped_prop = ("true" if "prop_to_true" in preprocess
                   else "false" if "not_to_false" in preprocess
                   else prop if projected_prop and prop in ("true", "false")
                   else None)
    if mapped_prop is not None and prop is not None and prop != mapped_prop:
        raise RenderError("prop_mismatch", "step.prop disagrees with preprocess", side="t1")
    if mapped_prop is None and prop is not None and preprocess:
        raise RenderError("prop_mismatch", "step.prop is present for a non-proposition preprocess operation", side="t1")
    return {"preprocess": preprocess, "source": source, "arg_id": arg_id,
            "extra_args": extra, "binders": binders, "discharge": discharge}


def render_side(side: Any, depth: int, source_text: Any = None,
                source_args: Any = None, operational: bool = False,
                introduced: dict[str, int] | None = None) -> str:
    """Render one entry of a conditional lemma's `side` array.

    A side trace has the same `steps`/`close` shape as a location, plus optional
    `intros` for an implication-shaped hypothesis (`c → x = u`, as `ite_congr`
    produces). It renders as T2's recursive side-proof grammar:
    `intro h ; explicit_rw [...] then <close>`, collapsing to just the close
    when there are no steps.
    """
    if not isinstance(side, dict):
        raise RenderError("bad_side", f"side entry is not an object: {side!r}")
    intros = side.get("intros") or []
    if not isinstance(intros, list):
        raise RenderError("bad_side", f"side.intros is not a list: {intros!r}")
    introduced = dict(introduced or {})
    prefix = ""
    for handle, name in enumerate(intros):
        # This is a recorder label used only to connect `assumption:` closes
        # and contextual locals to the deterministic handle.  It may be an
        # inaccessible or hygienic display name; it is never emitted.
        if not isinstance(name, str) or not name:
            raise RenderError("bad_intro_name", f"side.intros entry is not a name: {name!r}", side="t1")
        if name in introduced:
            raise RenderError("duplicate_introduced_name", f"side.intros repeats {name!r}", side="t1")
        introduced[name] = handle
        prefix += f"intro_ref {handle} ; "

    steps = side.get("steps") or []
    close = side.get("close")
    if steps:
        body = "explicit_rw [" + ", ".join(
            render_step(s, depth + 1, source_text=source_text,
                        source_args=source_args, operational=operational,
                        introduced=introduced)
            for s in steps
        ) + "]"
        if close is not None:
            body += " then " + render_close(close, introduced)
    elif close is not None:
        body = render_close(close, introduced)
    else:
        # No steps and no close discharges nothing; the recorder owes one.
        raise RenderError(
            "empty_side", "side trace has neither steps nor a close", side="t1"
        )
    return prefix + body


def _render_local(step: dict, introduced: dict[str, int]) -> str:
    local = step.get("local")
    if not isinstance(local, dict):
        raise RenderError("missing_local", "local-evidence rw has no local reference", side="t1")
    ctx_index = local.get("ctxIndex")
    if not isinstance(ctx_index, int) or isinstance(ctx_index, bool) or ctx_index < 0:
        raise RenderError("bad_local_ref", f"local.ctxIndex is invalid: {ctx_index!r}", side="t1")
    if local.get("contextual") is True:
        # T34 records the stable handle at the recorder boundary.  Contextual
        # locals commonly occur in a discharged side trace after the
        # intro_ctx event, so joining by its inaccessible display name (or by
        # finalizer file order) is unsound.  A missing handle remains a visible
        # trace defect; never recover one from the display name.
        handle = local.get("handle")
        if not isinstance(handle, int) or isinstance(handle, bool) or handle < 0:
            raise RenderError("missing_introduced_ref", "contextual local has no stable intro handle", side="t1")
        return f"introduced_ref {handle}"
    if local.get("inaccessible") not in (True, False):
        raise RenderError("bad_local_ref", "local.inaccessible is not boolean", side="t1")
    user_name = local.get("userName")
    name = step.get("name")
    result = f"local_ref {ctx_index}"
    if local.get("inaccessible") is True:
        return result
    if isinstance(user_name, str) and isinstance(name, str) and name != user_name:
        prefix = user_name + "."
        if not name.startswith(prefix):
            raise RenderError("local_name_mismatch", f"local name {name!r} does not extend {user_name!r}", side="t1")
        suffix = name[len(prefix):]
        if not suffix or any(part == "" or not part.isdigit() for part in suffix.split(".")):
            raise RenderError("bad_local_projection", f"local projection suffix is not numeric: {suffix!r}", side="t1")
        result += " " + "".join("." + part for part in suffix.split("."))
    return result


def render_rw(step: dict, depth: int, source_text: Any = None,
              source_args: Any = None, operational: bool = False,
              introduced: dict[str, int] | None = None) -> str:
    """`[← ]<term> at [pos][ with [...]]`.

    Legacy v1 `prop` steps use `eq_true`/`eq_false`; operational T16 derivations
    map proposition preprocessing to T17's fixed-redex `prop_true`/`prop_false`.
    Source-backed terms are taken verbatim from the T22 source span.
    """
    derivation = step.get("derivation")
    if operational and derivation is None:
        raise RenderError("missing_derivation", "fresh operational theorem rw has no derivation", side="t1")
    details = (_validate_derivation(step, derivation, source_text, source_args, operational, depth)
               if derivation is not None else None)
    preprocess = details["preprocess"] if details else []
    introduced = dict(introduced or {})
    if details and details["source"] == "simp-argument":
        term, source_direction = source_argument(source_text, source_args, details["arg_id"])
        term = check_term(term, "manifest simp argument")
        if step.get("dir") not in (None, source_direction):
            raise RenderError("direction_mismatch", "rw.dir disagrees with T22 sourceArgs.direction", side="t1")
    else:
        if details and details["source"] == "local-evidence":
            term = _render_local(step, introduced)
        else:
            term = check_name(step.get("name"), "rw.name")
        if details is None and step.get("prop") is not None:
            if step["prop"] not in ("true", "false"):
                raise RenderError("bad_prop", f"rw.prop is {step['prop']!r}, not 'true'/'false'")
            term = ("eq_true " if step["prop"] == "true" else "eq_false ") + atomize(term)
        # Operational theorem derivations never reuse the old recorder's
        # guessed/pretty-printed args for declaration origins. Matched and
        # instance binders are recovered by ExplicitRw at the fixed redex;
        # local-evidence keeps the established local reference/projection path.
        if details is None or details["source"] == "local-evidence":
            for arg in step.get("args") or []:
                term += " " + atomize(check_term(arg, "rw.args entry"))

    prop = step.get("prop")
    # A local simp argument such as `hh _` can be an iff theorem rather than
    # proposition evidence.  The recorder's proposition preprocessing label
    # is then historical simp bookkeeping: rendering it as `prop_true` asks
    # ExplicitRw for a proof of the left proposition and loses the iff's
    # rewrite direction.  Keep the source-backed iff term as an ordinary rw.
    local_iff = (
        details is not None
        and details["source"] == "simp-argument"
        and "prop_to_true" in preprocess
        and isinstance(step.get("local"), dict)
        and isinstance(step["local"].get("userName"), str)
        # A bare local proposition (`h`, `hp`, ...) is proposition evidence,
        # not an iff theorem.  Keep the historical local-iff path only when
        # the source argument carries additional application syntax (for
        # example `hh _`).
        and term.strip() != step["local"]["userName"]
    )
    projected_prop = any(op in preprocess for op in
                         ("conjunction_left", "conjunction_right",
                          "conjunction_projection"))
    mapped_prop = ("true" if "prop_to_true" in preprocess
                   else "false" if "not_to_false" in preprocess
                   else prop if projected_prop and prop in ("true", "false")
                   else None)
    wrapped_as_prop_step = False
    if mapped_prop is not None and not local_iff:
        prop_term = (lean_term(term) if details and details["source"] == "simp-argument"
                     else atomize(term))
        term = ("prop_true " if mapped_prop == "true" else "prop_false ") + prop_term
        wrapped_as_prop_step = True
    elif prop is not None and details is not None and not local_iff:
        if prop not in ("true", "false"):
            raise RenderError("bad_prop", f"rw.prop is {prop!r}, not 'true'/'false'")
        # Legacy v1 traces use eq_true/eq_false. Operational T16 traces use
        # the proposition-specific T17 forms above.
        term = ("eq_true " if prop == "true" else "eq_false ") + atomize(term)
        wrapped_as_prop_step = True

    if details and details["source"] == "simp-argument" and not wrapped_as_prop_step:
        term = lean_term(term)

    direction = step.get("dir", "fwd")
    if direction not in ("fwd", "rev"):
        raise RenderError("bad_dir", f"rw.dir is {direction!r}, not 'fwd'/'rev'")
    if details and details["source"] == "simp-argument":
        _, source_direction = source_argument(source_text, source_args, details["arg_id"])
        direction = source_direction
    if "reverse" in preprocess:
        if step.get("dir") not in (None, "fwd", "rev"):
            raise RenderError("bad_dir", f"rw.dir is {step.get('dir')!r}")
        direction = "rev"
    # A source argument is still written in the exact syntax supplied to
    # `simp`; only its leading direction marker was peeled above. The
    # `lean_term(...)` wrapper delimits it but does not rewrite its contents.
    out = ("← " if direction == "rev" else "") + term + " " + render_pos(step.get("pos"))

    sides = step.get("side")
    if sides:
        if not isinstance(sides, list):
            raise RenderError("bad_side", f"rw.side is not a list: {sides!r}")
        out += " with [" + ", ".join(
            render_side(s, depth, source_text=source_text, source_args=source_args,
                        operational=operational, introduced=introduced)
            for s in sides
        ) + "]"
    return out


def render_transport(step: dict, depth: int, *, source_text: Any = None,
                     source_args: Any = None, operational: bool = False,
                     introduced: dict[str, int] | None = None) -> str:
    """Render T35's dependent-forall transport event.

    The recorder already supplies the exact root-relative position, stable
    binder handle, and the two child event arrays. Keep those fields opaque:
    this function only validates their shape and recursively renders each
    recorded step. In particular, it does not recover a binder name, splice a
    term payload, or infer a body/domain position.
    """
    handle = step.get("handle")
    if not isinstance(handle, int) or isinstance(handle, bool) or handle < 0:
        raise RenderError(
            "bad_transport_handle",
            f"transport.handle is {handle!r}, not a non-negative integer",
            side="t1",
        )
    domain = step.get("domain")
    body = step.get("body")
    if not isinstance(domain, list):
        raise RenderError(
            "bad_transport_domain",
            f"transport.domain is not a list: {domain!r}",
            side="t1",
        )
    if not isinstance(body, list):
        raise RenderError(
            "bad_transport_body",
            f"transport.body is not a list: {body!r}",
            side="t1",
        )

    # `explicitRwInnerStep` intentionally excludes another transport. Refuse
    # it explicitly instead of emitting syntax the T2 parser cannot accept.
    for field, nested in (("domain", domain), ("body", body)):
        for nested_step in nested:
            if isinstance(nested_step, dict) and nested_step.get("kind") == "transport":
                raise RenderError(
                    "nested_transport",
                    f"transport.{field} contains a transport step, but T2's nested grammar does not admit it",
                    side="t2",
                )

    def render_nested(nested: list[dict]) -> str:
        rendered: list[str] = []
        for nested_step in nested:
            rendered.append(
                render_step(
                    nested_step,
                    depth,
                    source_text=source_text,
                    source_args=source_args,
                    operational=operational,
                    introduced=introduced,
                )
            )
        return ", ".join(rendered)

    return (
        f"transport forall {handle} [{render_nested(domain)}] body "
        f"[{render_nested(body)}] {render_pos(step.get('pos'))}"
    )


def _nonnegative_int(value: Any, what: str, reason: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise RenderError(reason, f"{what} is {value!r}, not a non-negative integer",
                          side="t1")
    return value


def _render_inner_steps(steps: Any, depth: int, *, source_text: Any = None,
                        source_args: Any = None, operational: bool = False,
                        introduced: dict[str, int] | None = None,
                        owner: str = "intro_ctx") -> str:
    if not isinstance(steps, list):
        raise RenderError("bad_intro_ctx_steps", f"{owner}.steps is not a list: {steps!r}",
                          side="t1")
    # T33's `explicitRwInnerStep0` deliberately excludes recursive structural
    # steps. Refuse these instead of emitting syntax the consumer cannot parse.
    forbidden = {"intro_ctx", "transport", "congr"}
    for nested in steps:
        if isinstance(nested, dict) and nested.get("kind") in forbidden:
            raise RenderError(
                "nested_intro_ctx_step",
                f"{owner}.steps contains {nested.get('kind')!r}, but T33's nested grammar does not admit it",
                side="t2",
            )
    return ", ".join(
        render_step(nested, depth + 1, source_text=source_text,
                    source_args=source_args, operational=operational,
                    introduced=introduced)
        for nested in steps
    )


def render_intro_ctx(step: dict, depth: int, *, source_text: Any = None,
                     source_args: Any = None, operational: bool = False,
                     introduced: dict[str, int] | None = None) -> str:
    """Render T34's stable contextual-introduction metadata using T33 syntax.

    The recorder's ``intro`` object is the complete identity contract. This
    function only validates and copies its numeric handles, positions and
    dependency indices; it never reads a display name or searches the local
    context for one.
    """
    if "name" in step:
        raise RenderError(
            "intro_ctx_display_name",
            "intro_ctx carries a display name; stable metadata must not use one",
            side="t1",
        )
    info = step.get("intro")
    if not isinstance(info, dict):
        raise RenderError("bad_intro_ctx", f"intro_ctx.intro is not an object: {info!r}",
                          side="t1")
    if "name" in info:
        raise RenderError(
            "intro_ctx_display_name",
            "intro_ctx.intro carries a display name; stable metadata must not use one",
            side="t1",
        )

    handle = _nonnegative_int(info.get("handle"), "intro_ctx.handle",
                              "bad_intro_ctx_handle")
    domain = info.get("domain")
    if not isinstance(domain, dict):
        raise RenderError("bad_intro_ctx_domain",
                          f"intro_ctx.domain is not an object: {domain!r}", side="t1")
    domain_pos = domain.get("position")
    dependencies = domain.get("dependencies")
    if not isinstance(dependencies, list):
        raise RenderError("bad_intro_ctx_dependencies",
                          f"intro_ctx.domain.dependencies is not a list: {dependencies!r}",
                          side="t1")
    for dependency in dependencies:
        _nonnegative_int(dependency, "intro_ctx domain dependency",
                         "bad_intro_ctx_dependency")

    scope = info.get("scope")
    if not isinstance(scope, dict):
        raise RenderError("bad_intro_ctx_scope",
                          f"intro_ctx.scope is not an object: {scope!r}", side="t1")
    scope_id = _nonnegative_int(scope.get("id"), "intro_ctx.scope.id",
                                "bad_intro_ctx_scope_id")
    operation = info.get("operation")
    owner = scope.get("owner")
    if not isinstance(operation, str) or not operation:
        raise RenderError("bad_intro_ctx_operation",
                          f"intro_ctx.operation is not a non-empty string: {operation!r}",
                          side="t1")
    if not isinstance(owner, str) or not owner:
        raise RenderError("bad_intro_ctx_scope_owner",
                          f"intro_ctx.scope.owner is not a non-empty string: {owner!r}",
                          side="t1")
    if owner != operation:
        raise RenderError("intro_ctx_scope_owner_mismatch",
                          "intro_ctx.scope.owner does not equal intro_ctx.operation",
                          side="t1")

    nested = _render_inner_steps(
        step.get("steps", []), depth, source_text=source_text,
        source_args=source_args, operational=operational, introduced=introduced,
    )
    deps = "[" + ", ".join(str(dependency) for dependency in dependencies) + "]"
    return (
        f"intro_ctx {handle} domain {render_pos(domain_pos)} deps {deps} "
        f"scope {scope_id} enter {render_pos(scope.get('enter'))} "
        f"exit {render_pos(scope.get('exit'))} with [{nested}] "
        f"{render_pos(step.get('pos'))}"
    )


def render_step(step: Any, depth: int = 0, *, source_text: Any = None,
                source_args: Any = None, operational: bool = False,
                introduced: dict[str, int] | None = None) -> str:
    """Render one STEP of the spec into one `explicit_rw` step."""
    if not isinstance(step, dict):
        raise RenderError("bad_step", f"step is not an object: {step!r}")
    kind = step.get("kind")
    if kind not in KNOWN_KINDS:
        # The spec makes an unknown kind a hard error for the replay tactic; it
        # is a hard error for the generator too.
        raise RenderError("unknown_kind", f"step kind {kind!r} is not in the spec")

    if kind == "rw":
        return render_rw(step, depth, source_text=source_text, source_args=source_args,
                         operational=operational, introduced=introduced)
    if kind == "unfold":
        return "unfold " + check_name(step.get("name"), "unfold.name") + " " + render_pos(
            step.get("pos")
        )
    if kind in REDUCTION_KINDS:
        # A named zeta event is zeta-delta: the recorder unfolded a local
        # definition and stores its user name.  The ordinary `zeta` replay
        # syntax contracts `letE`s only, and `unfold` accepts global constants,
        # so express this exact recorded result as a definitional `change`.
        # ExplicitRw checks that target against the selected subterm by defeq.
        # Keep the name validated as provenance; do not silently discard a
        # malformed name while turning it into a different step kind.
        if kind == "zeta" and "name" in step:
            check_name(step.get("name"), "zeta.name")
            if "local" in step:
                if not isinstance(step["local"], dict):
                    raise RenderError(
                        "bad_local_ref",
                        "named zeta local reference is not an object",
                        side="t1",
                    )
                if step["local"].get("contextual") is True:
                    raise RenderError(
                        "bad_local_ref",
                        "named zeta cannot target a contextual hypothesis",
                        side="t1",
                    )
                return (
                    "zeta_local "
                    + _render_local(step, dict(introduced or {}))
                    + " "
                    + render_pos(step.get("pos"))
                )
            after = check_term(step.get("after"), "zeta.after")
            return "change " + atomize(after) + " " + render_pos(step.get("pos"))
        if "name" in step:
            raise RenderError(
                "reduction_has_name",
                f"{kind} step carries a `name` field the spec does not define: "
                f"{step['name']!r}",
            )
        return kind + " " + render_pos(step.get("pos"))
    if kind == "change":
        return (
            "change "
            + lean_term(check_term(step.get("to"), "change.to"))
            + " "
            + render_pos(step.get("pos"))
        )
    if kind == "eq":
        by = step.get("by")
        if by not in ("rfl", "decide"):
            raise RenderError("bad_eq_by", f"eq.by is {by!r}, not 'rfl'/'decide'")
        lhs = check_term(step.get("lhs"), "eq.lhs")
        rhs = check_term(step.get("rhs"), "eq.rhs")
        return f"eq ({lean_term(lhs)} = {lean_term(rhs)}) by {by} " + render_pos(step.get("pos"))
    if kind == "congr":
        arg = step.get("arg")
        if not isinstance(arg, int) or arg < 0:
            raise RenderError("bad_congr_arg", f"congr.arg is {arg!r}, not an index")
        nested = step.get("steps")
        if not isinstance(nested, list) or not nested:
            raise RenderError("bad_congr", "congr step has no nested steps")
        if depth >= 2:
            # T2's grammar nests `congr` exactly two levels deep.
            raise RenderError(
                "congr_too_deep",
                f"congr nested {depth + 1} levels; the tactic grammar admits 2",
                side="t2",
            )
        inner = ", ".join(render_step(s, depth + 1, source_text=source_text,
                                        source_args=source_args,
                                        operational=operational,
                                        introduced=introduced) for s in nested)
        return f"congr {arg} [{inner}] " + render_pos(step.get("pos"))
    if kind == "transport":
        return render_transport(
            step,
            depth,
            source_text=source_text,
            source_args=source_args,
            operational=operational,
            introduced=introduced,
        )
    if kind == "intro_ctx":
        return render_intro_ctx(
            step,
            depth,
            source_text=source_text,
            source_args=source_args,
            operational=operational,
            introduced=introduced,
        )
    raise AssertionError(f"unhandled known step kind {kind!r}")


def collect_inaccessible(steps: list, out: list) -> None:
    """Collect, in first-use order, the `ctxIndex` of every inaccessible local.

    Retained for callers that inspect old v1 traces.  T23's indexed local
    handles mean the product renderer no longer emits ``rename_i`` names.
    """
    for step in steps:
        if not isinstance(step, dict):
            continue
        local = step.get("local")
        if isinstance(local, dict) and local.get("inaccessible"):
            idx = local.get("ctxIndex")
            if isinstance(idx, int) and idx not in out:
                out.append(idx)
        for side in step.get("side") or []:
            if isinstance(side, dict):
                collect_inaccessible(side.get("steps") or [], out)
        collect_inaccessible(step.get("steps") or [], out)


def render_location(loc: dict, depth: int = 0, *, source_text: Any = None,
                    source_args: Any = None, operational: bool = False) -> tuple[str, str | None]:
    """Render one location as (`explicit_rw` body, location clause or None)."""
    if not isinstance(loc, dict):
        raise RenderError("bad_location", f"location is not an object: {loc!r}")
    where = loc.get("loc")
    if where == "goal":
        clause = None
    elif isinstance(where, dict) and "hyp" in where:
        clause = "at " + check_name(where["hyp"], "location hyp name")
    else:
        raise RenderError("bad_location", f"location loc is {where!r}")

    steps = loc.get("steps")
    if not isinstance(steps, list):
        raise RenderError("bad_location", f"location steps is not a list: {steps!r}")
    body = "explicit_rw [" + ", ".join(
        render_step(s, depth, source_text=source_text, source_args=source_args,
                    operational=operational, introduced={})
        for s in steps
    ) + "]"
    if clause:
        body += " " + clause
    close = loc.get("close")
    if close is not None:
        if clause is not None:
            # The close belongs to the goal, not the rewritten hypothesis.
            # Route it through the closed side-proof grammar so exact terms are
            # bracket-delimited even when another unbulleted goal follows.
            body += "; explicit_rw [] then " + render_close(close)
        else:
            body += " then " + render_close(close)
    return body, clause


def render_trace(trace: dict, *, source_text: Any = None,
                 operational: bool | None = None) -> tuple[list[str], list[int]]:
    """Render a whole trace.

    Returns one tactic string per location, in order, plus the ordered
    `ctxIndex` list of inaccessible locals the caller turns into `rename_i`.
    The spec's multi-location forms (`at h ⊢`, `at *`) become one `explicit_rw`
    per location. A location close is unique and terminal: closes cannot be
    followed by another location's tactics.
    """
    if not isinstance(trace, dict):
        raise RenderError("bad_trace", "trace is not an object")
    # v2 wraps the same locations/steps in the source-site identity envelope;
    # the caller has already authenticated that envelope before rendering.
    if trace.get("schema") not in ("simp-trace-v1", "simp-trace-v2"):
        raise RenderError("bad_schema", f"schema is {trace.get('schema')!r}")
    locations = trace.get("locations")
    if not isinstance(locations, list) or not locations:
        raise RenderError("bad_trace", "trace has no locations")

    closing = [index for index, loc in enumerate(locations)
               if isinstance(loc, dict) and loc.get("close") is not None]
    if len(closing) > 1:
        raise RenderError(
            "multiple_location_closes",
            "trace has multiple location closes; their goal-closing order is ambiguous",
            side="t2",
        )
    if closing and closing[0] != len(locations) - 1:
        raise RenderError(
            "nonterminal_location_close",
            "a location close is followed by later location tactics",
            side="t2",
        )

    if operational is None:
        operational = trace.get("schema") == "simp-trace-v2"
    source_args = None
    site = trace.get("site")
    if isinstance(site, dict):
        source_args = site.get("sourceArgs")
    lines = [render_location(loc, source_text=source_text, source_args=source_args,
                             operational=operational)[0]
             for loc in locations]
    # T23 indexed local handles make inaccessible locals directly replayable;
    # no generated rename_i names or pretty-printed local names are needed.
    return lines, []


def unresolved_reason(trace: dict) -> str | None:
    """Return the classified `unresolved:` reason of a trace, if it has one.

    Older close-level classifications are encoded as `unresolved:<reason>` in
    `close.by`; current operational traces classify the individual event in
    its `unresolved` field. Either means that the call must stay visibly
    unresolved instead of sending a classified step through the renderer.
    """
    found: list[str] = []
    current_operational = trace.get("schema") == "simp-trace-v2"

    def scan_close(close: Any) -> None:
        if isinstance(close, dict):
            by = close.get("by")
            if isinstance(by, str) and by.startswith("unresolved:"):
                found.append(by[len("unresolved:") :])

    def scan_steps(steps: Any) -> None:
        if not isinstance(steps, list):
            return
        for step in steps:
            if not isinstance(step, dict):
                continue
            # The v2 recorder classifies a failed operation on the event
            # itself. Do not treat a same-named extension field on the trace,
            # site envelope, location, or arbitrary nested metadata as an
            # unresolved classification.
            reason = step.get("unresolved")
            if (current_operational and isinstance(reason, str) and reason
                    and step.get("kind") in KNOWN_KINDS):
                found.append(reason)

            # Visit only recursive step-bearing fields from the trace grammar;
            # this includes rewrite side proofs, congruence/introduction
            # substeps, and dependent-transport domain/body events.
            if step.get("kind") in {"rw"}:
                sides = step.get("side")
                if isinstance(sides, list):
                    for side in sides:
                        if isinstance(side, dict):
                            scan_steps(side.get("steps"))
                            scan_close(side.get("close"))
            if step.get("kind") in {"congr", "intro_ctx"}:
                scan_steps(step.get("steps"))
            if step.get("kind") == "transport":
                scan_steps(step.get("domain"))
                scan_steps(step.get("body"))

    locations = trace.get("locations")
    if isinstance(locations, list):
        for location in locations:
            if not isinstance(location, dict):
                continue
            scan_steps(location.get("steps"))
            scan_close(location.get("close"))
    if not found:
        return None
    return found[0]
