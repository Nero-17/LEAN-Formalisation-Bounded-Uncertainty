# Section 4 round three verification

The preserved baseline is `verification-section4-round2.json`: 112 mathematical modules and 744 handwritten declarations. Every baseline source SHA-256 must match before verification begins. Its previously verified compiled objects are reused.

`scripts/VerifySection4Round3.py --lean PATH --dependencies PATH` checks the pinned toolchain, exact source/import inventory and guarded declaration inventory. It freezes every source, freshly compiles all 6 added modules in dependency order with at most three compiler processes, then compiles the updated root. Every exit status is checked; errors, warnings and proof placeholders fail the run.

All 783 handwritten names are queried with Lean's builtin `#print axioms`, in three disjoint groups with the same root import. Each output must report exactly its input names, and only `propext`, `Classical.choice` and `Quot.sound` are permitted. Every source and both root/audit inputs are rechecked before success. Generated declarations are checked transitively through their dependencies.

The recorded run verifies 118 modules and 13842 source lines. This is an incremental rebuild of additions and root, not a fresh rebuild of the 112-module baseline. Historical compiler and audit evidence is preserved under its original filenames.

`verification-section4-round3-source-freeze.json`, the three `verification-section4-round3-axioms-*-input.lean` / `*-output.txt` pairs, and `verification-section4-round3.txt` contain this run's evidence. The independent semantic and integration review is `section4-round3-review.md`.
