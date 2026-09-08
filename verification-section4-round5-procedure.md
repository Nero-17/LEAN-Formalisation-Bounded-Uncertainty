# Section 4 round five verification

The preserved baseline is `verification-section4-round4.json`: 124 mathematical modules and 811 handwritten declarations. Every baseline source SHA-256 must match. Its previously verified compiled objects are reused.

`scripts/VerifySection4Round5.py --lean PATH --dependencies PATH` checks the pinned toolchain, exact source/import inventory and guarded handwritten declaration inventory. It freezes every source, freshly compiles all 14 additions in dependency order with at most three compiler processes, and compiles the updated root. Every exit status is checked; errors, warnings and proof placeholders fail the run.

`scripts/LeanInventory.py` handles named declarations, named instances, nested namespaces and named/anonymous sections. Unsupported private/opaque/class declarations, anonymous instances, proof placeholders and source-level axioms are rejected. The namespace and section stack must balance. The complete preserved 811-name baseline is retained. Positive and rejection probes covered vendor namespace/instance forms and attribute-plus-instance-binder declarations; an initially over-greedy attribute parser was rejected by baseline comparison and corrected before the final run.

All 939 handwritten names are queried with Lean's builtin `#print axioms`, in three disjoint groups with the same root import. Every output must report exactly its input names once. Only `propext`, `Classical.choice` and `Quot.sound` are permitted. The full foundation, final invariance-of-domain theorem and final original-scope 4.8 theorem are included, along with every named vendor helper and the finite-grid instance. Generated declarations are checked transitively through their dependencies. Source, root, audit input and inventory-tool hashes are rechecked before success.

The recorded run verifies 138 modules and 18620 source lines. It is an incremental rebuild of additions and root, not a fresh rebuild of the 124-module baseline. The source freeze, three input/output pairs and `verification-section4-round5.txt` preserve the actual evidence. The independent semantic and integration review is `section4-round5-review.md`.
