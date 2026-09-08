# Independent Section 4 round-four review

Research mode: Standard Research.

**Final decision: ACCEPT / verified and frozen.** All six additions passed independent semantic and integration review. The final run completed at `2026-09-08T22:45:16Z`: **124 modules, 14,336 source lines and 811 declarations**. All 118 baseline hashes are unchanged; six additions and the updated root compiled cleanly; three groups of 271, 270 and 270 builtin queries exactly cover every name and use only the permitted axioms. The fixed-weight scope estimate is **91% (85-96%)**, with moderately high confidence. The actual dual-ball atlas is proved; standalone Lemma 4.8 still lacks projection openness and its final arbitrary-manifold assembly. Section 4 is not complete. The unchanged published starting point is commit `f4f8d19cee20b2f62816374b490c7a3c5316b8b0`, with 118 modules, 13,842 lines and 783 declarations, whose accepted scope was **86% (80-92%)**. Earlier pending labels below are historical where superseded by this final ledger and acceptance.

Reviewer: persistent independent Agent 3 (`read_middle_history`). Standard Research was selected automatically because the fixed manuscript and existing one-sided graphs give a concrete route to the atlas obligation. The core review target is `max`; the inherited effective runtime setting is unknown and cannot be inspected or changed in this session. There is no user time or token limit. The reviewer may edit only this new report. The prior reports, proof sources, manuscript, README and verification infrastructure remain outside this reviewer's write scope. The user's Drive/TeX archive opt-out persists.

The initial checklist below was formed directly from the manuscript and pinned library definitions before accepting any new author result. The source remains manuscript commit `3200c88826c73210d1e83bfc46de1656ee0788ef`, SHA-256 `8F8D61DE1EB4E9672FF64B978FDC449316C666E0B92A0B72FC29FA16EE8A3911`. The previous report was independently confirmed unchanged at SHA-256 `C7685D08C6C9B80E35AD7FE6E912F2C6562C0C7D5681BB9C810CE133DF0D4A0F`.

## Fixed denominator and initial ledger

| Milestone | Fixed weight | Accepted baseline fraction | Contribution |
|---|---:|---:|---:|
| Source inventory | 10% | 1 | 10% |
| Forward 4.1-4.7, including the annulus witness | 25% | 1 | 25% |
| Regularity and iteration 4.8-4.11, including analytical point initialisation | 35% | 0.75 | 26.25% |
| Dual subsection, including substantive unnumbered geometry | 20% | 0.75 | 15% |
| Integration and permitted-axiom audit | 10% | 1 for the published baseline | 10% |

The weights and allowed fractions (0, 0.25, 0.5, 0.75, 1) are unchanged from earlier rounds. The total is 86.25%, reported as 86%. This measures completed mathematical scope, not proof size, elapsed work, correctness probability or compilation success. New sources receive no final integration credit from the earlier 783-query audit.

| Stable ID / inherited obligation | Exact acceptance target | Initial status | Strongest falsification check |
|---|---|---|---|
| R4-M01 / R3-M01 / R2-D02 | Genuine local half-space charts on the existing subtype topology of a closed regular domain with the proved one-sided boundary graphs | ACCEPT / PROVED | Both interior and boundary points have constructed source neighbourhoods and genuinely relatively open targets. Actual inverse laws and coverage are proved on the original subtype topology. |
| R4-M02 / model dimension | Identify the fixed product half-space with `EuclideanHalfSpace (Module.finrank R E)` | ACCEPT / PROVED | The genuine homeomorphism has dimension d, preserves the first coordinate and retains both subtype topologies. Positivity of d is discharged from the original system dimension assumption. |
| R4-M03 / dual-ball application | Construct a `ChartedSpace` on each actual dual ball and obtain a topological manifold with boundary, with compactness and C1 frontier independently linked to the same set | ACCEPT / PROVED | The actual standard-dimension atlas, compactness, Hausdorffness, second countability, star convexity and C1 frontier are assembled without extra assumptions. The atlas theorem has order zero and does not claim C1 transitions. |
| R4-T01 / S4-08a | Derive local openness of the injective projection of the arbitrary boundaryless topological hypersurface in Lemma 4.8 | OPEN | A graph, open projection, or regular closed set whose frontier is the given manifold is an extra hypothesis. Existing actual-frontier results do not prove this statement. |
| R4-T02 / S4-08b | Complete the original arbitrary-manifold C1 criterion and identify the given unit field as its normal | OPEN for the original assembly | The distinct-pair adapter is now proved, and the graph analysis was proved earlier. Neither establishes graph-domain openness; the final arbitrary-manifold assembly remains unproved. |
| R4-T03 / first step of 4.8 | Convert the original distinct-endpoint hypothesis to uniform all-pairs bounds and little-o, then derive local orthogonal projection injectivity | ACCEPT / PROVED | Diagonal bad pairs are impossible in the contradiction proof; no nonisolated-point, manifold, projection-openness or graph assumption is added. |
| R4-V01 | Preserve all 118 baseline source hashes and reconcile every new frozen proof, build result, declaration and permitted-axiom query | ACCEPT / PROVED for the final snapshot | All 124 source hashes and line counts match; six additions and root compiled cleanly; every one of the 811 current names appears exactly once in the three complete permitted-axiom groups. |

## Independent source and interface assessment

The dual subsection assumes the whole-space self-diffeomorphism setting and a positive lower radius bound. The unnumbered paragraph following Definition 4.13 says that each dual ball is a compact d-dimensional manifold with boundary, is star-shaped, and has a C1 hypersurface frontier. These are separate assertions. Compactness, star-shapedness and the concrete C1 frontier/one-sided graphs were proved in the frozen baseline. The remaining atlas assertion is topological: an actual half-space `ChartedSpace`, together with `IsManifold` of order zero, is sufficient for this wording. No C1 compatibility of the chosen atlas is needed unless that stronger result is explicitly claimed.

The pinned mathlib definitions were inspected directly: `Geometry/Manifold/ChartedSpace.lean:138` requires an atlas of actual `OpenPartialHomeomorph` values, a preferred chart at every point, source coverage and atlas membership, on the already supplied topology. `Geometry/Manifold/Instances/Real.lean:58` defines `EuclideanHalfSpace d` as the nonnegative first-coordinate subtype of real Euclidean d-space; line 178 gives its genuine model with corners. `Geometry/Manifold/IsManifold/Basic.lean:854` derives order-zero manifold compatibility once the genuine charted-space structure exists. This instance is not itself a construction of the atlas.

Boundary charts must straighten the proved one-sided graph and include the zero-height boundary in their relative half-space target. Any continuous extension of a local graph may be used only where agreement and continuity have been proved; no global C1 property follows from a merely continuous extension. Interior charts must map an open neighbourhood to an open subset of the strictly positive half-space. The resulting preferred charts must cover both cases using closedness and the actual frontier/interior decomposition. A fixed model must be used throughout, not a point-dependent horizontal type.

The source of Lemma 4.8 was reread at lines 2166-2208. Its topological hypersurface has the subspace topology and is boundaryless. The proof obtains projection injectivity from the two-moving-point secant condition, then explicitly uses invariance of domain to obtain an open projection image. The new atlas construction for dual balls does not supply that openness for arbitrary topological hypersurfaces. Replacing the manifold by the frontier of a regular closed set would invoke a stronger interface. Extending a locally Lipschitz graph over its projected subset would still leave the same-dimensional subset's openness unproved. A one-dimensional chart argument using order and the intermediate value theorem would cover only a special dimension. No new source error follows from this unresolved formalisation prerequisite.

There is a direct reason that the analytic secant hypothesis cannot remove the topological openness obligation: let the given topological manifold already lie in a fixed hyperplane and take the constant perpendicular unit normal. Every secant numerator is then zero. The original conclusion must still show local openness in that hyperplane. Thus a general proof needs an appropriate topological openness result even in this special case. This reduction is the new focused assessment; it does not infer impossibility from an unsuccessful library search.

## Review gate for new results

New author modules will first be checked against these exact hypotheses and local inverse/topology obligations. Actual compiler success will then establish proof acceptance for the checked source version. The final gate is independent reconciliation of the frozen source hashes, complete declaration inventory, successful builds and builtin permitted-axiom query outputs. No final progress increase or report freeze is justified before that gate.

## First static model review

`HalfSpaceModel.lean` was read in full before its final compilation result was supplied. Its continuous linear equivalence joins the distinguished real coordinate with exactly d-1 remaining coordinates. The first-coordinate identity is proved in both directions. Restricting the actual homeomorphism by this identity constructs the correct nonnegative-coordinate subtype homeomorphism and proves the model-boundary coordinate equivalence. This is semantically faithful; final source hash and compiler evidence are still pending. The helper takes `NeZero d`, which must be derived at the system application rather than added as an independent restriction.

Final model update: all ten declarations, including the later finite-dimensional ambient coordinate equivalence, compiled with exit code zero and no warnings. The final source hash was independently matched to `1955AA215E2ACDF5319DAB8DE5B35831F2FB5242C5277099B6CC7F5690DB6A17`. The added helper constructs the ambient equivalence from the actual finite-rank equality; it introduces no instance registration or mathematical axiom. Overall integration remains a separate gate.

## First static distinct-secant review

`DistinctSecants.lean` was read in full before its final compiler result. The uniform bound is obtained by contradiction: bad pairs at radii 1/(n+1) must be distinct because the strict bad inequality cannot hold on the diagonal. They converge to the marked point, so the original distinct-endpoint sequence hypothesis contradicts the positive error bound after dividing by a strictly positive chord norm. This proves the uniform estimate including diagonal pairs without assuming a nonisolated point or even membership of the marked point in the set.

The little-o theorem transports that estimate to the actual within-filter on the product set, using the maximum product distance to control both endpoints. The local projection theorem uses the real orthogonal projection `value - inner normal value * normal` (scalar multiplication in the source) and the unit-normal hypothesis. Equal projections make the chord parallel to the normal; the uniform one-half estimate then forces a zero chord. These statements are semantically faithful. Compiler/hash evidence is pending, and neither the adapter nor local injectivity proves projection-image openness or full Lemma 4.8.

## First static atlas review

`RelativeHomeomorph.lean`, `BoundaryAtlas.lean` and `ChartedSpaceModelTransport.lean` were read in full. The generic relative restriction starts with an actual ambient homeomorphism and an equivalence of set membership on an open ambient neighbourhood. Its chart source is the subtype preimage of that neighbourhood; its target is the other subtype's preimage under the ambient inverse. Both are genuinely relatively open. Local membership identifies the actual forward and backward maps, proving both inverse laws and continuity on the respective sources. Total fallback values only make the maps defined away from these local sets; they do not supply any assumed inverse property or global continuity.

The boundary chart uses the proved continuous extension only inside its agreement ball, and reverses the height so that membership is exactly nonnegative first coordinate. The interior chart shifts affine coordinates by a strictly positive first coordinate and restricts to the actual interior. Every point of the set subtype is covered by the interior/frontier split. The preferred-chart range is an actual atlas. The change-of-model definition composes each real chart with the genuine model homeomorphism, preserving source coverage and the existing topology. All three constructions are semantically accepted; final compiler evidence, frozen hashes and the dual-system application remain pending at this checkpoint.

Baseline preflight independently matched all 118 proof hashes and all 13,842 source lines to the published manifest. The unchanged toolchain file hash is `DB7BB24B756D745BBDE83FE92718B51BD3625DAE3701BA0F598D0EEDCD3F3028`; the unchanged lake configuration hash is `924C9C345D1D2F4BEC28CBA1B41E8A6A09B5541D147D44DC92E2DA82C35193E3`.

The final compiled sources of the generic atlas were independently matched to the author-supplied clean compilation hashes: `RelativeHomeomorph.lean`, `41CC728CBDEA66DBCC0856FE2D54142EB8FA201AB20F733E97AD9C7DEB6C37A5`; and `BoundaryAtlas.lean`, `D4F43F2DAF8A7D0F001FC53F3B7ED9D41AF8616481FBAED8AB72A9235BD63518`. Both have exit-zero, warning-free compiler evidence. The complete round-wide audit remains pending.

## First static dual-system application review

`DualBallManifold.lean` was read in full. The half-space dimension positivity and finite dimensionality are derived from the system's existing dimension-at-least-two field. The chart family comes from the already proved actual dual-ball one-sided graphs, then the genuine generic atlas, then the proved model homeomorphism. It is a constructed local instance, not an assumed `ChartedSpace` parameter.

The final theorem explicitly combines compactness, Hausdorffness, second countability, the order-zero manifold with the standard d-dimensional half-space model, star convexity and the same actual set's C1 frontier. The metric/subtype topology is never replaced. Pointwise positive radius is weaker than the manuscript's uniform positive lower bound. No global smooth extension, chart assumption, dependency upgrade or unnecessary self-map assumption enters this geometric result. Semantic disposition: ACCEPT, pending the final source version's clean compilation and the integrated audit.

If the final evidence gate passes, the fixed fractions become 1 / 1 / 0.75 / 1 / 1, giving 91.25%, reported as **91% (85-96%)**, with moderately high confidence. The entire dual milestone would close. The distinct-secant adapter and local projection injectivity are substantive progress, but do not raise the regularity milestone above 0.75 while original Lemma 4.8 still lacks projection openness. This is a conditional scope assessment, not final verification acceptance.

## Frozen-source and driver preflight

All six final mathematical sources match the individually verified clean compiler versions. The final projection proof's algebraic rewrite was reread; it retains exactly the same projection and unit-normal argument. The final dual-ball application was reread in full. The unchanged 118-source baseline contains 783 declarations; this round adds six modules and 28 declarations, giving **124 modules, 14,336 lines and 811 declarations** (680 theorems, 123 definitions and eight structures). The guarded source inventory was independently reconciled with every root import, freeze row and builtin query name. No proof placeholder, added axiom, unsafe declaration, `native_decide`, unsupported namespace or unregistered declaration form was found.

| New module | Independently matched final SHA-256 |
|---|---|
| `ChartedSpaceModelTransport` | `203976943921DF909E00C8CCDD06B284794F77FC72076DAC6778FBB17C519E02` |
| `DistinctSecants` | `0789D433C30E701FB0DA1AD9E442FC8CD071D1C39863ECCAB247ABE0F1BCEE1A` |
| `HalfSpaceModel` | `1955AA215E2ACDF5319DAB8DE5B35831F2FB5242C5277099B6CC7F5690DB6A17` |
| `RelativeHomeomorph` | `41CC728CBDEA66DBCC0856FE2D54142EB8FA201AB20F733E97AD9C7DEB6C37A5` |
| `BoundaryAtlas` | `D4F43F2DAF8A7D0F001FC53F3B7ED9D41AF8616481FBAED8AB72A9235BD63518` |
| `DualBallManifold` | `BA1E57E890019F8CE63AE0013BD337FEA46EB0318423F767CE32BC2AFFD34C01` |

`scripts/VerifySection4Round4.py` was independently read in full. It preserves the previously verified 118-module baseline, rebuilds all six additions when their project dependencies are ready, rejects diagnostics and nonzero exits, and replaces each new compiled object only after successful compilation and source-hash checking. It then compiles the root and runs three disjoint groups of builtin `#print axioms` queries, covering all 811 registered names. It checks exact output coverage, permitted axioms and unchanged source/root/audit hashes. The permitted set is exactly `propext`, `Classical.choice`, and `Quot.sound`. This is an incremental fresh build of six modules plus root, with a complete current-name axiom audit; it is not a fresh build of all 124 modules or a single uninterrupted compilation of the whole audit file.

| Preflight input | SHA-256 |
|---|---|
| Root entry point | `95F1E26CF02FD7FE2DF0C2057AD517154B39D274C5DD37B5D1967BC525505831` |
| `AxiomAudit.lean` | `9BDAB4358CB3602D326A636EB1029AC2170DA577DD9871E17C318E1EB6DD1453` |
| Round-four source freeze | `1D1AFE4B1F2E7992D1A0C6B5981FE84BDA9965545E15BA7B4423B77DDCD1E63D` |
| Round-four driver | `535685B37A81CF51FE143BE31DBA6B19E942F5A911117A17C2D3EBA0FF489026` |

The final result file, complete outputs and final source reconciliation remain pending at this preflight checkpoint.

## Final independent integration acceptance

The completed result at `2026-09-08T22:45:16Z` was independently reconciled with the root imports, all mathematical sources, the preserved round-three baseline, the freeze, the full public log and every input/output pair. All 124 source hashes and 14,336 line counts match. All 118 baseline rows are unchanged. The guarded source-name inventory contains exactly the same 811 unique names as `AxiomAudit.lean` and the three query inputs. Each input is exactly the common root import plus its intended builtin queries; the groups contain 271, 270 and 270 distinct names. Every output reports its exact input set once. Their union is the whole current inventory, and every reported axiom belongs to the permitted three-element set. No error, warning or `sorryAx` occurs.

The six new per-module compiler outputs are empty. The public compile records contain every addition exactly once and are consistent with project dependency order: model transport, half-space model, distinct secants, relative homeomorphism, boundary atlas, then dual-ball application. The root success record follows all six. The combined log contains the complete three outputs and the final success marker. The source freeze, root, audit input and driver hashes remain identical to preflight. The previous independent report, manuscript, toolchain and lake configuration remain unchanged. The actual pinned mathlib checkout was separately confirmed at `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; no dependency upgrade was used.

| Final evidence | SHA-256 |
|---|---|
| Result JSON | `F4C6B4B1467F7795760A23FB8D1E9F314A61727724808AF78DEE955471FB8963` |
| Public compiler/audit log | `FC3B0F2A44A3B5E1AF46B3D1AE3D7695527BE03156957BDBC7B59EAFBC9D26F0` |
| Query group 1 input | `A5E956658EBC463751D3D15C40D34B4263938CDF1CFB387EF0AE7B829F50645F` |
| Query group 1 output | `C7A63BFEB52309F2C68D88247726632F506752B606C580FF4E1DA1A2397E484A` |
| Query group 2 input | `27100FB0F5DDA06522BC769B173BC90B9CE2EDE4FA69EA9C01495A6A7FEF5F6A` |
| Query group 2 output | `04BF66D659741B80F4E4A3F15B71D6CDC2D075BBB98FFD9EC9089E96D8FB248E` |
| Query group 3 input | `39537ED0BC47675638FF2E2B2B5FD98FB3F92DD3E7FB700D9A74F3FF5F81565F` |
| Query group 3 output | `CC92A3B33BC9AC16691CDEAA59060B8809E728E9EC5CCB979886DFE0B7C1F51E` |

The publication finalizer draft was read without executing it. Its proposed manifest and README preserve the topological atlas/C1 frontier distinction, explicitly leave Section 4 incomplete, describe the exact incremental build, retain historical evidence and make no numerical certification or manuscript-edit claim. Publication and archive creation remain the parent agent's subsequent actions.

## Final fixed-weight estimate and stopping assessment

| Milestone | Unchanged weight | Final fraction | Contribution |
|---|---:|---:|---:|
| Source inventory | 10% | 1 | 10% |
| Forward 4.1-4.7 | 25% | 1 | 25% |
| Regularity and iteration 4.8-4.11, including analytical point initialisation | 35% | 0.75 | 26.25% |
| Dual subsection, including substantive unnumbered geometry | 20% | 1 | 20% |
| Integration and permitted-axiom audit | 10% | 1 | 10% |

The fixed total is 91.25%, reported as **91% (85-96%)**, with moderately high confidence. The range reflects the coarse allocation of the remaining standalone topological lemma within the regularity milestone; it is not a probability of correctness. The dual milestone is closed by actual proved atlas data and the final audit, not by increased module count. The analytical first step of 4.8 earns no additional coarse milestone fraction while the projection-openness obligation remains unresolved.

This bounded round stops after verified completion of the actual atlas and the original distinct-secant/local-injectivity step, with no outstanding defect in those submitted proofs. The remaining substantive task is to prove an appropriate topological openness result for the arbitrary boundaryless manifold in its actual subspace topology, then connect it to the already proved graph analysis. No such openness theorem or graph has been inserted as an assumption to claim original Lemma 4.8. The fixed-hyperplane reduction above explains why the missing obligation survives even when all normal secants vanish identically. It does not show that the manuscript theorem is false or that formalisation is impossible.

No new source error was found in this round, and no manuscript was edited. The earlier arbitrary-set distance-sublevel scope issue and the withdrawn Section 3 Definition 3.9 overinterpretation retain their recorded dispositions. Numerical figures and trajectories remain outside the certified deductive scope. Section 4 is not claimed complete.

This independent report is now frozen. Any subsequent publication or archive consistency check is read-only and must retain this exact reviewed snapshot.
