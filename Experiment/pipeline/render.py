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

* `rw`     -> `[← ]<term> at [pos][ with [side, ...]]`, where `<term>` is
              `name` (wrapped by `eq_true`/`eq_false` when `prop` is set)
              followed by its parenthesised `args`.
* `unfold` -> `unfold <name> at [pos]`
* `beta`/`eta`/`proj`/`zeta`/`iota` -> `<kind> at [pos]`
* `change` -> `change <to> at [pos]`
* `eq`     -> `eq (<lhs> = <rhs>) by <by> at [pos]`
* `congr`  -> `congr <arg> [<nested steps>] at [pos]`
* `intro_ctx` -> unrenderable; T2 documents it as recognised-but-unimplemented,
              so a trace containing one is a classified render failure rather
              than a step that silently vanishes.

Closes map through one table: `rfl`/`decide`/`omega`/`nofun` render as
themselves, `true_intro` as `exact True.intro`, `assumption:<n>` as
`exact <n>`, `absurd:<h>` as `exact <h>.elim`. Anything else, including every
`unresolved:<reason>`, is not a close this renderer invents a spelling for.
"""

from __future__ import annotations

import re
from typing import Any

# Spec step kinds. `intro_ctx` is listed so an unknown kind stays distinguishable
# from a known-but-unrenderable one.
REDUCTION_KINDS = ("beta", "eta", "proj", "zeta", "iota")
KNOWN_KINDS = ("rw", "unfold", "change", "eq", "congr", "intro_ctx") + REDUCTION_KINDS

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

    `args`, `change.to`, `eq.lhs`/`eq.rhs` are all written into T2's whitelisted
    term grammar. Three shapes are known not to survive it and are refused by
    name rather than shipped into a parse error: the elision marker `⋯` (which
    is pretty-printer output, not a term), embedded newlines or `have`/`let`
    telescopes, and `pp.all` universe/`nat_lit` annotations.
    """
    if not isinstance(text, str) or not text.strip():
        raise RenderError("bad_term", f"{what} is not a non-empty string: {text!r}")
    if "⋯" in text:
        raise RenderError("elided_term", f"{what} contains the elision marker ⋯: {text!r}")
    if "\n" in text:
        raise RenderError("multiline_term", f"{what} contains a newline: {text!r}")
    if re.search(r"(?<![\w.])(have|let|match|do|fun\b.*=>.*\bby)\b", text):
        raise RenderError(
            "non_term_syntax", f"{what} carries tactic/telescope syntax: {text!r}"
        )
    if ".{" in text or re.search(r"(?<![\w.])nat_lit\b", text):
        raise RenderError(
            "pp_all_term",
            f"{what} is pp.all output (universe levels / nat_lit): {text!r}",
        )
    if "✝" in text:
        raise RenderError(
            "inaccessible_name", f"{what} splices an inaccessible name: {text!r}"
        )
    if "by " in text or text.strip().endswith(" by"):
        raise RenderError("term_has_by", f"{what} contains a `by` block: {text!r}")
    return text.strip()


def render_pos(pos: Any) -> str:
    """`[0, 1, 1]` -> `at [0, 1, 1]`; `[]` -> `at []`."""
    if not isinstance(pos, list) or not all(
        isinstance(i, int) and i >= 0 for i in pos
    ):
        raise RenderError("bad_pos", f"pos is not a list of child indices: {pos!r}")
    return "at [" + ", ".join(str(i) for i in pos) + "]"


def atomize(term: str) -> str:
    """Parenthesise a compound term so application binds as intended.

    `args` entries and `prop`-wrapped names are applied, so `f a` as an argument
    must become `(f a)`. Already-parenthesised and atomic terms are left alone.
    """
    term = term.strip()
    if not term:
        raise RenderError("bad_term", "empty term")
    if IDENT_RE.fullmatch(term):
        return term
    if term.startswith("(") and term.endswith(")"):
        # Only when the outer parens actually match, so `(a) + (b)` is wrapped.
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


def render_close(close: Any) -> str:
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
    if by in ("rfl", "decide", "omega", "nofun"):
        return by
    if by == "true_intro":
        return "exact True.intro"
    if by.startswith("assumption:"):
        return "exact " + check_name(by[len("assumption:") :], "close.by assumption")
    if by.startswith("absurd:"):
        return "exact " + check_name(by[len("absurd:") :], "close.by absurd") + ".elim"
    if by.startswith("unresolved:"):
        raise RenderError("unresolved_close", f"close.by is {by!r}", side="t1")
    raise RenderError("unknown_close", f"close.by {by!r} is not a spec close form")


def render_side(side: Any, depth: int) -> str:
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
    prefix = ""
    for name in intros:
        prefix += "intro " + check_name(name, "side.intros entry") + " ; "

    steps = side.get("steps") or []
    close = side.get("close")
    if steps:
        body = "explicit_rw [" + ", ".join(render_step(s, depth + 1) for s in steps) + "]"
        if close is not None:
            body += " then " + render_close(close)
    elif close is not None:
        body = render_close(close)
    else:
        # No steps and no close discharges nothing; the recorder owes one.
        raise RenderError(
            "empty_side", "side trace has neither steps nor a close", side="t1"
        )
    return prefix + body


def render_rw(step: dict, depth: int) -> str:
    """`[← ]<term> at [pos][ with [...]]`.

    The `prop` flag is the spec's `p = True` / `¬p = False` convention: simp
    uses a Prop-valued fact as an equation, and replay writes the ordinary
    lemma `eq_true`/`eq_false` around it. `args` are the explicit arguments the
    recorder captured, each parenthesised when compound.
    """
    term = check_name(step.get("name"), "rw.name")
    prop = step.get("prop")
    if prop is not None:
        if prop not in ("true", "false"):
            raise RenderError("bad_prop", f"rw.prop is {prop!r}, not 'true'/'false'")
        term = ("eq_true " if prop == "true" else "eq_false ") + atomize(term)
    for arg in step.get("args") or []:
        term += " " + atomize(check_term(arg, "rw.args entry"))

    direction = step.get("dir", "fwd")
    if direction not in ("fwd", "rev"):
        raise RenderError("bad_dir", f"rw.dir is {direction!r}, not 'fwd'/'rev'")
    out = ("← " if direction == "rev" else "") + term + " " + render_pos(step.get("pos"))

    sides = step.get("side")
    if sides:
        if not isinstance(sides, list):
            raise RenderError("bad_side", f"rw.side is not a list: {sides!r}")
        out += " with [" + ", ".join(render_side(s, depth) for s in sides) + "]"
    return out


def render_step(step: Any, depth: int = 0) -> str:
    """Render one STEP of the spec into one `explicit_rw` step."""
    if not isinstance(step, dict):
        raise RenderError("bad_step", f"step is not an object: {step!r}")
    kind = step.get("kind")
    if kind not in KNOWN_KINDS:
        # The spec makes an unknown kind a hard error for the replay tactic; it
        # is a hard error for the generator too.
        raise RenderError("unknown_kind", f"step kind {kind!r} is not in the spec")

    if kind == "rw":
        return render_rw(step, depth)
    if kind == "unfold":
        return "unfold " + check_name(step.get("name"), "unfold.name") + " " + render_pos(
            step.get("pos")
        )
    if kind in REDUCTION_KINDS:
        # The spec defines no `name` on a reduction step and T2 has no syntax
        # for one, so a step that carries one is reported rather than dropped.
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
            + check_term(step.get("to"), "change.to")
            + " "
            + render_pos(step.get("pos"))
        )
    if kind == "eq":
        by = step.get("by")
        if by not in ("rfl", "decide"):
            raise RenderError("bad_eq_by", f"eq.by is {by!r}, not 'rfl'/'decide'")
        lhs = check_term(step.get("lhs"), "eq.lhs")
        rhs = check_term(step.get("rhs"), "eq.rhs")
        return f"eq ({lhs} = {rhs}) by {by} " + render_pos(step.get("pos"))
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
        inner = ", ".join(render_step(s, depth + 1) for s in nested)
        return f"congr {arg} [{inner}] " + render_pos(step.get("pos"))
    # intro_ctx
    raise RenderError(
        "intro_ctx",
        "contextual simp step: the tactic recognises `intro_ctx` but does not "
        "implement it",
        side="t2",
    )


def collect_inaccessible(steps: list, out: list) -> None:
    """Collect, in first-use order, the `ctxIndex` of every inaccessible local.

    The spec makes `ctxIndex` a `LocalDecl.index` that identifies a declaration;
    it is explicitly *not* a `rename_i` argument. A generator derives `rename_i`
    names from the order of inaccessible declarations in the context, so the
    ordering here is by context index, not by first use.
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


def render_location(loc: dict, depth: int = 0) -> tuple[str, str | None]:
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
    body = "explicit_rw [" + ", ".join(render_step(s, depth) for s in steps) + "]"
    if clause:
        body += " " + clause
    close = loc.get("close")
    if close is not None:
        if clause is not None:
            # T2 is explicit that the `then` clause applies to the goal; a
            # hypothesis rewrite leaves its closer to the next line. Nothing in
            # this corpus exercises it, so refuse rather than guess.
            raise RenderError(
                "close_on_hyp",
                "location rewrites a hypothesis and also carries a close; the "
                "tactic's `then` clause applies to the goal only",
                side="t2",
            )
        body += " then " + render_close(close)
    return body, clause


def render_trace(trace: dict) -> tuple[list[str], list[int]]:
    """Render a whole trace.

    Returns one `explicit_rw` line per location, in order, plus the ordered
    `ctxIndex` list of inaccessible locals the caller turns into `rename_i`.
    The spec's multi-location forms (`at h ⊢`, `at *`) become one `explicit_rw`
    per location; they are separate tactics because each names its own location.
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

    inaccessible: list[int] = []
    for loc in locations:
        if isinstance(loc, dict):
            collect_inaccessible(loc.get("steps") or [], inaccessible)
    lines = [render_location(loc)[0] for loc in locations]
    return lines, sorted(inaccessible)


def unresolved_reason(trace: dict) -> str | None:
    """Return the classified `unresolved:` reason of a trace, if it has one.

    The spec classifies an unreplayable call by writing `unresolved:<reason>`
    into a `close.by`. Such a site renders as the original call plus a marker
    comment, so the module still compiles and the site is counted, never hidden.
    """
    found: list[str] = []

    def scan(obj: Any) -> None:
        if isinstance(obj, dict):
            close = obj.get("close")
            if isinstance(close, dict):
                by = close.get("by")
                if isinstance(by, str) and by.startswith("unresolved:"):
                    found.append(by[len("unresolved:") :])
            for value in obj.values():
                scan(value)
        elif isinstance(obj, list):
            for item in obj:
                scan(item)

    scan(trace)
    if not found:
        return None
    return found[0]
