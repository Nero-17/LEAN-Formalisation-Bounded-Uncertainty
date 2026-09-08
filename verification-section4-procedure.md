# Section 4 verification procedure

This is an incremental extension of the verified Section 3 project. It adds 18 mathematical modules and 127 handwritten declarations, for 87 modules and 637 declarations in total.

## Preserved baseline

`verification-section3.json` is a byte-preserving copy of the preceding manifest. All 69 mathematical source hashes match that manifest. Their previously checked compiled objects are reused. The original full Section 3 rebuild and 510-declaration audit remain in `verification.txt` and the original three axiom-query groups. Historical manifests and logs describe their own snapshots, including the older entry point and README.

## Current verification

`scripts/VerifyIncremental.py` performs the following checks:

1. Match every baseline mathematical source hash and require its compiled object.
2. Require exact agreement between the entry-point imports and all mathematical source files.
3. Erase nested Lean comments and strings, check the current namespace/declaration conventions, and extract all handwritten declaration names. Require exact equality with `AxiomAudit.lean`. This is a guarded parser for this project's syntax, not a general Lean parser. A separate broader declaration scan independently confirmed the same 637 names.
4. Check the Lean version and commit against the preserved manifest. The mathlib HEAD was independently checked as `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
5. Freeze all 87 source hashes, then freshly compile every added module, with at most three processes and only after its added dependencies pass. Reject errors and warnings before replacing each compiled object.
6. Compile the updated project entry point.
7. Partition all 637 builtin `#print axioms` queries into three disjoint groups with the identical project import. Require exactly the expected reports in each group, successful Lean exit, and no errors or warnings. Permit only `propext`, `Classical.choice`, and `Quot.sound`.
8. Recheck every frozen mathematical source hash and the root/audit inputs before writing the successful result.

The current evidence is `verification-section4.txt`, `verification-section4-source-freeze.json`, and the three `verification-section4-axioms-*-input.lean` / `*-output.txt` pairs. `verification.json` records the current aggregate scope and hashes. This run is not a fresh rebuild of all 87 modules.

## Reproduction

The portable full-source route is:

```text
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

For the original cached Windows environment, invoke:

```text
python scripts/VerifyIncremental.py --lean PATH_TO_PINNED_LEAN_EXE --dependencies PATH_TO_PINNED_PACKAGE_DIRECTORY
```

The incremental script deliberately fails if the baseline compiled objects are absent. In a clean checkout, use the full-source Lake route. Build and audit verification establishes the checked Lean statements and their dependencies; source-faithfulness and unfinished paper obligations are separately recorded in `section4-coverage-review.md`.
