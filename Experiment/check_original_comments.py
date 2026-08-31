#!/usr/bin/env python3
"""Verify that original calls are inert, recoverable, and do not eat suffixes."""
from pathlib import Path
import subprocess
import tempfile

from check_simp_engine_boundary_source import preserve_original_call

ROOT = Path(__file__).resolve().parents[1]


def main():
    originals = [
        "simp only [Nat.add_zero]",
        'simp only [show \"-/\" = \"-/\" from rfl]',
        "simp only [show n + 0 = n from by\n    simp only [Nat.add_zero]]",
        'simp only [show \"/-\" = \"/-\" from rfl]',
    ]
    for original in originals:
        rendered = preserve_original_call("skip\n  skip", original, "  ")
        lines = rendered.split("\n")
        recovered = "\n".join(line[len("  -- "):] for line in lines[2:-1])
        assert recovered == original
        assert lines[0] == "skip" and lines[-1] == "  skip"
    # These use ordinary deterministic tactics to isolate source layout from
    # recording or selector logic, including unobserved terminal-only forms.
    snippets = []
    def inline(before, tactic, after, original):
        indent = " " * (len(before.rsplit("\n", 1)[-1]) + 2)
        return before + preserve_original_call(tactic, original, indent) + after
    snippets.append(inline("example : True := by ", "exact True.intro", "\n", originals[0]))
    snippets.append(inline("example : True := by ", "skip", "; exact True.intro\n", originals[1]))
    snippets.append(inline("example : True ∧ True := ⟨by ", "exact True.intro", ", True.intro⟩\n", originals[3]))
    snippets.append(inline("example : True := by\n  first\n  | ", "fail", "\n  | exact True.intro\n", originals[2]))
    snippets.append(inline("example : Nat := by\n  ", "skip", "\n  exact 0\n", originals[0]))
    with tempfile.TemporaryDirectory(prefix="original-comments-", dir=ROOT / ".lake") as raw:
        path = Path(raw) / "Comments.lean"
        path.write_text("import Lean\n\n" + "\n".join(snippets))
        completed = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                   text=True, capture_output=True, timeout=120)
        if completed.returncode:
            raise RuntimeError(completed.stdout + completed.stderr)
    print("original comments: exact recovery, embedded delimiters, inline/layout/suffix cases: ok")


if __name__ == "__main__":
    main()
