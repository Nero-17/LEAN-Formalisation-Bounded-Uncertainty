# Section 4 round two verification

The preserved baseline is `verification-section4-round1.json`: 87 mathematical modules and 637 handwritten declarations. Every baseline source SHA-256 must match before verification begins. Its previously verified compiled objects are reused.

`scripts/VerifySection4Round2.py --lean PATH --dependencies PATH` checks the pinned toolchain, exact source/import inventory and the guarded declaration inventory. It freezes every source, freshly compiles all 25 added modules in dependency order with at most three compiler processes, and then compiles the updated root. Every exit status is checked; errors, warnings and proof placeholders fail the run.

All 744 current handwritten names are queried using Lean's builtin `#print axioms`, in three disjoint groups with the same root import. Each output must report exactly its input names, and only `propext`, `Classical.choice` and `Quot.sound` are permitted. Every source and both root/audit inputs are rechecked before success is recorded. Generated declarations are checked transitively through their dependencies.

The recorded run verifies 112 modules and 13122 source lines. It is an incremental rebuild of additions and root, not a fresh rebuild of the 87-module baseline. The historical compiler and audit evidence is preserved under its original filenames.

`verification-section4-round2-source-freeze.json`, the three `verification-section4-round2-axioms-*-input.lean` / `*-output.txt` pairs, and `verification-section4-round2.txt` contain this run's evidence. The independent semantic and integration review is `section4-round2-review.md`.
