# Search-free Mathlib campaign

Updated 2026-09-01T14:45:00+00:00

- Current closed-world inventory: 83,627 calls in 8,264 modules.
- Scope partition after the reviewed quoted-tactic rule: 83,556 direct calls and 71 reusable calls; zero unresolved.
- Scheduling partition: 6,280 direct-only modules, 40 reusable-containing modules, and 1,944 modules with no executable call.
- Accepted translated-tree coverage: 0 calls in 0 modules. Historical per-module reports remain triage evidence only.
- Manual proof database: 16 exact overrides across 14 modules; every original call is preserved as a comment.

The final clean manifest is the next publication boundary. The preceding diagnostic manifest found five caller-dependent quoted tactics; the focused postprocessor proves that exactly those five unique IDs become reusable and no other corpus record changes. Production dispatch excludes every reusable-containing module until the caller-dependent recorder and replay oracle are available.

The source-bound dependency map already joins all 8,264 Mathlib modules and has no external Mathlib dependency gap. The old four-module exclusion and external-digest workaround is retired. Complete acceptance still requires current per-module reports, a composed translated source tree, and a cold dependency-order build with independent declaration and replay checks.

Next work:

1. Publish and strictly source-verify the clean exact-HEAD manifest.
2. Import it with the 8,264-module dependency map and rerun the eight former pilot failures using the 16-entry manual database.
3. Dispatch the 6,280 direct-only modules under allowance and 12 GiB free-space guards.
4. Record and replay all 71 reusable calls with authenticated caller/configuration/state variants.
5. Cold-certify the complete translated tree, then normalize replacement readability and continue with other search tactics.
