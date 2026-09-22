# T67 Lake no-cache review

Verdict: PASS for `0f53a76b911af8273442c6452280038172ca74a4`. No provider calls were made.

The bootstrap invokes exactly `lake --no-cache exe cache get`: `--no-cache` is a Lake global option before the `exe` subcommand, so it disables Lake's own package build-cache downloads while still running the Mathlib `cache get` executable. The following `lake build ...` remains a separate command. The generated bootstrap is checked for this exact placement. `set -eu` remains at the start of the remote script, so a failed cache-get command still stops bootstrap before the build/worker launch. The change does not alter authorization, one-host/$20/TTL, checksum, or dispatch gates.

Local `lake --help` documents `--no-cache` as “build packages locally; do not download build caches.” The attempted executable `--help` would initialize the Mathlib dependency and was interrupted; no provider calls were made and the worktree remains clean.

Offline checks:

- `python3 -B Experiment/check_scaleway_simp_replacements.py` — 19 full-run mock checks passed.
- `python3 -B Experiment/check_simp_replacement_jobs.py` — 10 tests passed.
- `python3 -B -m py_compile Experiment/scaleway_simp_replacements.py Experiment/check_scaleway_simp_replacements.py` — passed.
- `git diff --check` — passed.
