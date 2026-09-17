# T11 tracker trusted-environment reconciliation

Updated `tracking/campaign.json` for the user's trusted-environment
clarification. The active phase now records T1 and T4's simplified v2 mapping
implementations as running: module path, original character range, exact call
text, source ordinal, and complete invocation ordinals. Hashes, nonces, byte
authentication, and a standalone forgery suite are explicitly out of scope.

T10 is recorded as cancelled. T7's declaration oracle is retained as an
optional focused diagnostic only. The acceptance statement is now explicit:
source-preserving replacement of the pinned simp family, successful translated
dependency-tree compilation, then full Mathlib compilation and a zero
remaining-call audit. Coverage remains unchanged and whole-tree acceptance is
still zero.

Preserved unchanged: historical coverage and cached evidence, AWS account,
authorization, budget, resource-cleanup and deadline records, historical
tracker references, and all existing evidence hashes.

Checks passed:

- `python3 -m json.tool tracking/campaign.json`
- `python3 -B Experiment/check_campaign_status.py` (9 tests)
- semantic invariants: preserved coverage/AWS/deadline/authorization/history,
  zero acceptance, T1/T4 running, T10 cancelled, T7 optional
- `git diff --check`
