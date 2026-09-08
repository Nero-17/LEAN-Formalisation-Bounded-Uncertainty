# Independent Section 4 round-three review

Research mode: Standard Research.

**Final decision: ACCEPT / verified and frozen.** All six additions closing the annulus witness, later point-start inclusion, actual nearest-distance derivative and inverse-E display have passed independent semantic and integration review. The run completed at `2026-09-08T17:30:57Z`: **118 modules, 13,842 source lines and 783 handwritten declarations**. All 112 baseline hashes are unchanged; six additions and the updated root compiled cleanly; three groups of 261 builtin queries cover every name and use only the permitted axioms. The final fixed-weight scope estimate is **86% (80–92%)**, with moderately high confidence. Standalone Lemma 4.8 and an actual half-space atlas for dual balls remain OPEN; Section 4 is not complete. The published starting point is commit `9f3cdf632411a0eaf77909b54117cbf4ed156acb`, whose scope was **80% (74–87%)**. Earlier OPEN/pending labels below are historical where superseded by the current ledger and final acceptance.

Reviewer: independent persistent Agent 3 (`read_middle_history`). Standard Research was selected automatically because the remaining claims are explicitly inventoried and several have concrete routes through existing proofs. Core review target: `max`; this persistent session cannot inspect or change its actual runtime effort, so the effective inherited setting is unknown. There is no user time or token limit. This reviewer may write only this new report, and does not modify proof sources, previous reports, the manuscript, README, verification scripts or manifests. The user's Drive/TeX archive opt-out persists. No Overleaf edit is authorised by this review task.

The initial evidence assessment below was made independently from the manuscript and pinned library sources before receiving new proof-author conclusions. Agreement among authors is not used as proof evidence. The manuscript is the fixed online commit `3200c88826c73210d1e83bfc46de1656ee0788ef`, SHA-256 `8F8D61DE1EB4E9672FF64B978FDC449316C666E0B92A0B72FC29FA16EE8A3911`.

## Unchanged denominator and initial ledger

| Milestone | Fixed weight | Accepted baseline fraction | Baseline contribution |
|---|---:|---:|---:|
| Source inventory | 10% | 1 | 10% |
| Forward 4.1–4.7 | 25% | 0.75 | 18.75% |
| Regularity and iteration 4.8–4.11, including analytical point initialisation | 35% | 0.75 | 26.25% |
| Dual subsection, including substantive unnumbered geometry | 20% | 0.75 | 15% |
| Integration and permitted-axiom audit | 10% | 1 for the published baseline | 10% |

Fractions remain restricted to 0, 0.25, 0.5, 0.75 and 1. The weights were fixed before the first Section 4 results and are not changed here. Progress measures completed mathematical scope, not time spent, proof size, correctness probability or successful compilation alone. New sources require their own final integration evidence; the earlier 744-query audit certifies only the earlier snapshot.

| Stable round-three ID / earlier obligation | Exact acceptance target | Initial disposition | Decisive objection or boundary case |
|---|---|---|---|
| R3-T01 / S4-08a | Derive a locally open, injective projection for the arbitrary boundaryless topological hypersurface in Lemma 4.8, in its actual subspace topology | OPEN | A supplied graph, open projection or regular-closed domain whose frontier is M is a stronger interface. Existing actual-frontier proofs do not close the arbitrary-manifold statement. |
| R3-T02 / S4-08b | Connect that derived graph to its C1 derivative and identify the supplied continuous unit field as normal | OPEN for original assembly; graph analysis already PROVED | The manuscript's condition uses distinct moving pairs. Any all-pairs formulation must prove the adapter or derive the diagonal case explicitly. Graph differentiation alone does not prove graph-domain openness. |
| R3-A01 / S4-01b | Give an actual contracting system and compact regular closed annulus whose inner boundary is not source-visible | ACCEPT / PROVED | `AnnulusVisibility` proves the exact inflated ball and every inner-boundary constituent ball's interior containment, with the actual system and genuine source C1 chart family. Final hash matches clean compilation. |
| R3-I01 / S4-12b | Connect the first-step singleton fibre theorem with all later set-valued iterations and actual beta iterates | ACCEPT / PROVED | `PointStartIteration` proves the actual positive-iterate frontier inclusion, including the first-step case, with domain preservation and the correct iteration shift. It assumes no later smoothness or visibility and claims no unjustified equality. |
| R3-D01 / R2-D03 | Prove the actual distance derivative at an exterior point with a unique nearest point in the original source set | ACCEPT / PROVED for compact sets and closed sets in proper spaces | The compact proof derives selector localisation and the actual radial gradient from uniqueness only at the marked point. `ClosedDistanceDifferentiability` proves an exact compact localisation and transfers the gradient. All three hashes match clean compilation; round-wide integration remains separate. |
| R3-D02 / inverse-E display following 4.16 | Prove the actual inverse-exponential image of the source inward bundle equals the dual inward bundle | ACCEPT / PROVED | `DualExponentialInverse` constructs the inverse of the actual proved whole-space sphere-bundle bijection, proves its left inverse law there, and derives the inward-bundle inverse image with target regular closedness discharged from nearest attainment. |
| R3-M01 / R2-D02 packaging | Give an actual manifold-with-boundary structure for each dual ball, beyond its already proved local one-sided graphs | OPEN | The subtype must retain its actual topology, charts must cover interior and boundary, and targets must be open in a fixed half-space model. C1 atlas compatibility, if claimed, must be proved. |
| R3-V01 | Preserve all 112 baseline source hashes and reconcile every newly frozen source, declared name, successful build and permitted-axiom query | ACCEPT / PROVED for the final round-three snapshot | All 118 source hashes and 13,842 lines match; all 112 baseline hashes are unchanged; six additions and root compiled cleanly; all 783 names exactly match source, inputs and three complete permitted-axiom output groups. |

## Source scope and initial falsification checks

Notation 3.3 explicitly makes A nonempty compact regular closed throughout Sections 3 and 4 unless stated otherwise. The dual definitions and setwise factorisation explicitly quantify arbitrary A; later statements and their surrounding prose need to be read with that distinction. The previous round already proved generic attained-nearest wrappers for 4.16–4.17, so no compactness ambiguity remains in those accepted correspondences. The source does not impose convexity on A. For maps on X or a sphere bundle, the existing local ambient-extension convention still governs derivatives and regularity.

The annulus discussion and caption at manuscript lines 1874–1905 make a concrete analytical claim: the inner source component can disappear from the inflated frontier, so source visibility is not automatic. An independently checked candidate is the identity system on the plane, constant radius one, and A given by `1 <= norm x <= 2`. Its inflation should equal the closed ball of radius three. Every constituent ball centred on the unit inner circle lies in the closed ball of radius two, hence strictly inside the inflated ball. This is a testable proof target, not yet a Lean result. Compactness, regular closedness and any claimed C1 source boundary must be connected to that same actual set.

Lemma 4.8, lines 2166–2208, starts with an arbitrary topological codimension-one manifold in the subspace topology. Its proof obtains local projection injectivity from the two-moving-point condition and then invokes invariance of domain for projection openness. The preceding round's criterion is stronger at its input: it applies to the actual frontier of a regular closed domain. That domain supplies the connected-cap crossing argument. It cannot be silently supplied for arbitrary M. The unqualified manifold is read in the conventional boundaryless sense; allowing manifold boundary would change the conclusion's scope. No counterexample under the intended hypotheses has been found.

The point-start discussion at lines 2780–2791 follows Proposition 4.11's positive initial radius assumption. The exact first image is a genuine closed ball, its normal bundle comes from one beta step, and Theorem 4.10 can then be applied to that ball for subsequent iterations. Its general conclusion is an inclusion. The numerical panels remain illustrative rather than certified exact trajectories, and connecting the analytical inclusion must not create an equality claim for all projected iterates.

The distance assertion immediately before 4.16, lines 2889–2897, concerns actual infimum distance and a unique nearest point at one marked exterior point. Compact A is sufficient under the standing scope. A nearby selected minimiser need not be unique. For the intended proof, compactness and uniqueness at the marked point force any choices of nearby minimisers to converge to that point; the squared-distance comparison then gives the derivative, and positivity permits composition with square root. This route needs actual selector convergence, not an assumption of it.

The inverse-E display at lines 2911–2918 follows from the actual whole-space bijection of the sphere bundle and the accepted forward inward-bundle equality. This should be a connected theorem about the inverse map already constructed from the system's canonical radius data. It needs no new normal calculation or stronger nearest-point hypothesis.

The dual-ball paragraph at lines 2855–2859 asserts compactness, dimension d, a manifold with boundary, star-shapedness and C1 frontier. The previous round proves the geometric facts and explicit one-sided C1 graphs. What remains in R3-M01 is an actual atlas/model interface. The paragraph does not demand infinite differentiability of the domain atlas when the radius is only C1.

## Independent pinned-library search

Search date: 2026-09-08. The primary source is installed mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, under `C:/Users/lzysh/Documents/Codex/bounded-noise-asymptotic-periodicity/.lake/packages/mathlib/Mathlib`. Whole-tree searches covered invariance of domain and dimension, Brouwer and Jordan–Brouwer, and continuous-injective/open-map combinations. Follow-up reads inspected manifold charts and open partial homeomorphism constructors. No applicable invariance-of-domain theorem was located. Hits involving open embeddings either assume an open map or use an existing open/local-homeomorphism structure. This is a statement about the searched pinned tree, not every Lean library or the mathematical truth of 4.8.

For manifold packaging, the following exact APIs were opened and checked rather than inferred from names:

| Primary source location | Verified API and usable scope |
|---|---|
| `Geometry/Manifold/ChartedSpace.lean:138` | `ChartedSpace` requires an atlas of actual `OpenPartialHomeomorph` charts, a preferred chart at every point, source coverage and atlas membership. It uses the already supplied topology of the subtype. |
| `Geometry/Manifold/Instances/Real.lean:58` | `EuclideanHalfSpace n` is the actual nonnegative-first-coordinate subtype, with n nonzero. |
| Same file, line 178 | `modelWithCornersEuclideanHalfSpace` is the standard half-space model; the model map is the subtype inclusion, and its total inverse clamps the first coordinate. |
| Same file, line 269 | `IccLeftChart` is a concrete example of building an `OpenPartialHomeomorph` from a closed subset to a half-space. Its source/target openness and both inverse laws are proved, not inferred from set membership. |
| `Geometry/Manifold/IsManifold/Basic.lean:799` | `isManifold_of_contDiffOn` obtains a Cn manifold from actual chart-transition `ContDiffOn` proofs in model coordinates. It does not supply charts or transition differentiability. |
| Same file, line 854 | With a genuine charted-space structure already present, an `IsManifold I 0 M` instance is available. This is sufficient for the topological manifold part; claiming C1 compatibility requires additional transition proofs. |
| `Topology/OpenPartialHomeomorph/Constructions.lean:259` | `subtypeRestr` applies to an open subtype. It cannot directly restrict an ambient open chart to the closed dual ball. |
| `Topology/Maps/Basic.lean:673` | `IsOpenEmbedding.of_continuous_injective_isOpenMap` requires openness as a hypothesis and therefore cannot replace invariance of domain. |

Searches in the manifold instances for closed-ball atlas shortcuts did not locate an applicable existing closed-ball structure. A proof route is nevertheless concrete: use the already derived one-sided graph to straighten boundary neighbourhoods into the half-space and standard interior neighbourhoods into its interior; construct the actual subtype partial homeomorphisms; select a covering chart family; then invoke the appropriate manifold API. If a C1 structure is claimed, transition functions must be locally identified with compositions of the genuine C1 graph formulas. The continuous Tietze extension used for global topological straightening in the earlier graph bridge is not globally C1 and must not be treated as such.

## Initial review plan and progress

The independent acceptance tests are now fixed. New theorem statements will be checked against the actual paper scope and construction dependencies before any author verdict is adopted. Specific probes include: diagonal secants; empty inputs; zero initial radius versus the positive-radius singleton claim; nonclosed f(X) outside the whole-space dual case; uniqueness only at one nearest point; chart targets open in the half-space topology; and derivative/order compatibility of local chart transitions.

The baseline remains **80% (74–87%)**, moderately high confidence. None of these searches or proof plans earns new completion credit. The next useful work is the exact annulus and iteration/inverse interfaces, the actual unique-nearest-point derivative, and the concrete half-space atlas construction. The generic 4.8 projection-openness step remains a distinct substantial obligation. Standard Research will continue through concrete advancement and repair cycles, and stop only when the assigned review is complete, a verified obstacle makes the next attempt unproductive, or further work no longer changes a material claim. Missing library infrastructure will be distinguished from a false source statement.

## First implementation checkpoint

**AnnulusVisibility: static semantic ACCEPT; compilation pending.** The complete proposed source was read independently. It uses the actual existing whole-plane identity system of radius one and the actual set `closedBall 0 2 minus ball 0 1`. Its compactness, interior, regular closedness, frontier and nonemptiness are proved. The exact union inflation is the closed ball of radius three: radial rescaling handles norms below one and above two, the original point handles the middle interval, and zero is treated separately using a concrete unit vector. The reverse containment is the triangle inequality.

The global defining polynomial `(norm x squared - 1) * (norm x squared - 4)` is nonpositive exactly on this annulus. Its gradient `(4 * norm x squared - 10) times x` is nonzero on each actual boundary circle. The code constructs genuine C1 defining data and common one-dimensional frontier graphs from that calculation, rather than assuming source smoothness. For every inner-circle centre, its entire constituent ball has norm at most two and therefore lies strictly inside the actual inflated ball of radius three. The final theorem connects this exclusion to the actual `SourceVisible` predicate and includes the actual system contraction. This is the manuscript's stated annulus mechanism with one exact choice of radii, not a numerical certification of the displayed figure. R3-A01 will receive PROVED status only after the final source is matched to a clean compilation.

**NearestPointContinuity: static semantic ACCEPT; clean compilation reported, final hash reconciliation pending.** The complete source was read independently. The selected point comes from actual compact distance attainment, with membership and exact distance equality proved. For each positive neighbourhood radius around the unique minimiser, the compact source outside that ball is either empty or has an attained strictly larger distance from the marked point. Strictness follows from uniqueness at that point alone. A one-third gap bound and the triangle inequality then force every nearby minimiser into the ball. The proof quantifies over all nearby minimisers; it does not assume their uniqueness. It derives convergence and pointwise continuity of the chosen selector and does not claim global continuity.

**DistanceDifferentiability: static semantic ACCEPT; final compilation pending.** Both minimising inequalities are used with their correct direction. The marked minimiser is a competitor at the nearby point, giving the upper squared-distance remainder bound by the squared displacement. The nearby minimiser is a competitor at the marked point; expanding about it and applying the inner-product bound gives the lower remainder bound by minus twice its distance from the marked minimiser times the displacement. The final absolute bound is therefore valid. The selector-convergence theorem makes its multiplying factor tend to zero, yielding the actual Fréchet derivative of squared infimum distance. No derivative of the selector is used. The exterior-point hypothesis and actual attained source membership make the base distance nonzero; nonnegative real infDist allows square root of its square to be identified with actual distance everywhere. This gives the stated radial gradient. Compact nonempty A and completeness are sufficient under the manuscript's Euclidean standing scope; no convexity or extra radius/system assumption appears.

**PointStartIteration: static semantic ACCEPT; final compilation pending.** The complete source was read independently. The first theorem proves the exact iteration-shift identity. The system theorem applies the already accepted full 4.10 inclusion to the genuine first closed ball, which is compact, lies in X by the system ball condition, and has genuine C1 boundary from its positive radius. Every initial ball normal pair is then recovered from the actual first-step beta fibre image. The ambient/typed iteration agreement connects the subsequent n steps to the original fibre's n+1 steps. The conclusion is the correct inclusion for every positive set-valued iterate; n=0 in this statement gives the already exact first-step case. No smooth intermediate boundary or visibility assumption is added, and no equality of all later projected shapes is claimed.

**Nearest-distance final compilation: ACCEPT / PROVED.** The independently recomputed final hashes are `37EB8D6126F8EFE4675AE0D92E3658745B740D7FF31C050C89F55C98F486AC27` for `NearestPointContinuity` and `12E0E5135573D9EA473AEEF19242BE0BA2937803EEC1BEF6D523965DDF8AED92` for `DistanceDifferentiability`. Both match the author's clean successful compilation. Their statements and proofs retain the reviewed hypotheses. This closes R3-D01 under the manuscript's nonempty compact standing scope; it does not assert the same theorem for arbitrary nonclosed A. The new declarations still require final round-wide source and axiom reconciliation.

**DualExponentialInverse: static semantic ACCEPT at the supplied interface; generic final wrapper pending.** The complete proposed source was read independently. It defines the actual exponential lift on the whole-space unit sphere bundle, proves injectivity through the existing actual exponential-map theorem and surjectivity through the existing whole-space result, and only then forms its inverse equivalence. The ambient representative agrees with that actual inverse on unit normals; its identity value off the sphere is unconstrained and is not used in an inverse claim. The inward-bundle identity follows from the accepted forward image equality and this genuine left inverse on unit normals. The current final statement explicitly takes dual-inflation regular closedness. That property is already proved from first-side nearest attainment in the frozen baseline, so a wrapper discharging this parameter has been requested to match the generic original-scope interface. This is a small connection gap, not a false inverse calculation.

## Closed analytical claims and final connection checks

**AnnulusVisibility: ACCEPT / PROVED.** The independently recomputed final SHA-256 is `243A69042B3939DFE932B8BCED20F82866B395C31D77E52FEFDB0F8C2AE30887`, matching the author's successful compilation without warnings. The final common-model chart uses the explicit finite-dimensional identity for the plane. The final boundary case splits and chart reparametrisation were reread, and the original mathematical hypotheses and conclusions are unchanged. R3-A01 is closed.

**ClosedDistanceDifferentiability: ACCEPT / PROVED.** The complete source was read independently and the final SHA-256 `82BBF59B389FF9E1E4C537D059CD4E5615611B7C5CDE6F87A5DA96970A6F4A3B` was recomputed and matched to clean compilation. For a closed source in a proper metric space, the proof intersects the source with the closed ball about y of radius `dist(y,x) + 2`. This compact set contains x. If w lies within distance one of y, any attained nearest point z of the original closed source satisfies `dist(y,z) <= 2 dist(w,y) + dist(y,x)`, so z lies in that compact truncation. Both directions of the infimum-distance inequality are proved, giving exact equality of the actual two distance functions on a full neighbourhood of y.

The marked value and uniqueness transfer to the truncation. The earlier compact theorems then give both the squared-distance and exterior-distance gradients, and eventual equality transfers them to the actual original source. No nearby uniqueness, convexity or differentiable projection is assumed. Properness supplies compact balls and nearest attainment, and includes the original finite-dimensional Euclidean setting. This strengthens R3-D01 beyond compact A to closed A in the stated proper setting; it does not claim a theorem for arbitrary nonclosed sets.

**Inverse-E scope connection: statically resolved; final compilation pending.** The added `image_exponentialInverseOnAmbient_of_two_sided_nearest` wrapper was read directly. It derives the dual-inflation regular-closed witness from the existing first-side nearest-attainment theorem and invokes the actual inverse-bundle identity. The final statement therefore has no extra dual regularity parameter, no compactness assumption and no stronger nearest-point condition than the already accepted generic 4.16 interface.

**Baseline preservation check: PASS.** A separate read-only reconciliation confirms all 112 published mathematical source hashes remain unchanged, the previous round's frozen review still has SHA-256 `B4C003D2015628377E72D2043764B07A0BF0975F00D55ABBE63A2835DBA9F5AA`, and the fixed manuscript hash is unchanged. Final new-source and axiom verification is still pending.

With the annulus witness closed, the prospective fixed fractions after the remaining proposed connections and a successful new audit are `1 / 1 / 0.75 / 0.75 / 1`, giving **86.25%**, reported as **86% (80–92%)**, with moderately high confidence. The unproved arbitrary-manifold Lemma 4.8 keeps the regularity milestone at 0.75; the unconstructed actual half-space atlas keeps the dual milestone at 0.75. Closing the distance and inverse displays does not justify declaring that entire dual milestone complete while the atlas remains open. These are prospective scope figures until the new integration succeeds.

## Final semantic source reconciliation and integration preflight

**Point-start and inverse-E final sources: ACCEPT / PROVED.** Both final files were reread at their connections to the existing actual system maps. `PointStartIteration` now explicitly uses `boundaryFormulaOnAmbient_apply`, then the proved typed/ambient iteration equality and its first projection; this resolves elaboration without altering any assumption or conclusion. The no-extra-regularity inverse-E wrapper is included in the final compiled file. The independently recomputed hashes match the parent's successful compilation without warnings.

| New module | Final independently checked SHA-256 |
|---|---|
| `AnnulusVisibility` | `243A69042B3939DFE932B8BCED20F82866B395C31D77E52FEFDB0F8C2AE30887` |
| `NearestPointContinuity` | `37EB8D6126F8EFE4675AE0D92E3658745B740D7FF31C050C89F55C98F486AC27` |
| `DistanceDifferentiability` | `12E0E5135573D9EA473AEEF19242BE0BA2937803EEC1BEF6D523965DDF8AED92` |
| `ClosedDistanceDifferentiability` | `82BBF59B389FF9E1E4C537D059CD4E5615611B7C5CDE6F87A5DA96970A6F4A3B` |
| `PointStartIteration` | `DEA8B67FA133E704A9891D5531509D0BE13A35101737FDAFBD1613A649C669BD` |
| `DualExponentialInverse` | `66FE3A63C91BD51C7F92252FF854096899A26FB25CC59DA68C990C3428888155` |

**Verification driver: static ACCEPT; execution acceptance pending.** The complete `VerifySection4Round3.py` was read. It preserves `verification-section4-round2.json` as the 112-module baseline, verifies source hashes before reuse, matches the complete mathematical-file and root-import inventories, and matches guarded source declaration names to the audit input. It rebuilds each addition only after its dependencies have completed, checks exits and diagnostics, then compiles the updated root. Three disjoint builtin-query groups must exactly match their inputs and use only the permitted axioms. Every source and the root/audit inputs are rechecked before writing a success result. This is an incremental rebuild of six additions and root with reused baseline objects, not a fresh rebuild of all 118 modules.

**Independent preflight: PASS.** A separate read-only reconciliation found exactly 118 mathematical modules, 13,842 source lines and 783 different handwritten names: 663 theorems, 112 definitions and eight structures. The six additions contain 39 new declarations. All 112 baseline source hashes remain unchanged; all 118 source hashes and line counts match the new freeze; root imports match all source files; and the source-extracted names equal the complete audit input. The planned three groups have 261 names each and partition all 783 names. The original manuscript hash is unchanged.

| Verification input | Independently recomputed SHA-256 |
|---|---|
| `BoundedUncertainty.lean` | `210D166EB56431FC63730DAD571FDF6728629FB0EB15A6DED81522C4CFC31326` |
| `AxiomAudit.lean` | `4DD0ED4E230CC19BC9250CF087222273791D3225B9234A61A18D6C550B31F43B` |
| `verification-section4-round3-source-freeze.json` | `5A650DC6A14D8A51C904058D05D0D8FD71A9BEEEA2ED1B8B69945E41B038D1B1` |
| `scripts/VerifySection4Round3.py` | `5470EF8FA4478E76FBB41ABBCB2D75E238FBC79663E6185DD1BA31B42382C0F0` |

This preflight validates the final inputs; it is not a claim that all builtin queries have finished. R3-V01 remains OPEN until actual successful outputs and the final post-run snapshot are independently reconciled.

## Final integration acceptance, fixed progress and freeze

**R3-V01: ACCEPT / PROVED.** The final driver result records success at `2026-09-08T17:30:57Z`. An independent read-only reconciliation verified the actual result, combined compiler log, all six query input/output files, frozen mathematical sources and preserved baseline:

- The 118 mathematical source files exactly match the root imports and result/freeze inventory. Every source hash and line count matches, totalling 13,842 lines. All 112 published baseline hashes remain unchanged, and the six additions are exactly the reviewed modules.
- The source inventory contains exactly 783 different handwritten names: 663 theorems, 112 definitions and eight structures. They exactly match `AxiomAudit.lean`, with no omitted or duplicate name and no proof placeholder in the mathematical sources.
- The public log contains one successful clean compilation record for each of the six additions and a separate successful root compilation after them. The order respects every mathematical dependency. All six per-module diagnostic outputs are empty.
- The three input files contain exactly the intended disjoint round-robin groups of 261 names and the same root import. Each output reports exactly its own input names, without duplicates, errors or warnings. Their union is exactly all 783 names. Every dependency axiom belongs to `{propext, Classical.choice, Quot.sound}`.
- The public combined log contains those three complete outputs and exactly all 783 reports. Its success markers and the result fields agree with the independently checked evidence. Source, root, audit-input, freeze and driver hashes match preflight. The manuscript and the previous frozen review hashes are unchanged.

This is an incremental verification of six additions and root, reusing the previously verified 112 baseline objects. It is not a fresh compilation of all 118 modules. The builtin queries were fully executed in three disjoint groups; no single uninterrupted compilation of the complete audit source is claimed. Kernel dependency reporting checks generated dependencies transitively through the audited handwritten names.

| Final verification evidence | Independently recomputed SHA-256 |
|---|---|
| `.lake/build/section4-round3-verification/result.json` | `7BC414436EF75C53988618610AC5149ABBF56016E489A4B20993AB497F913050` |
| `verification-section4-round3.txt` | `D92F8D14AC636E950DB08341173B57B7A52638E1E80BF3660741979481669B2C` |
| `verification-section4-round3-axioms-1-input.lean` | `50A2BE8467B0A1CA537FAD0998624CD620EC1289C983FF47F1B8DF78D78D7B0B` |
| `verification-section4-round3-axioms-1-output.txt` | `4FD90EFBF2240D545993D88218DE20184DFE7B691CEB708C898FF163D52461FD` |
| `verification-section4-round3-axioms-2-input.lean` | `5D8FFECEBD7FE801FC6D1C56284006CBD197A60A02B8F68786A9C31D1E21F571` |
| `verification-section4-round3-axioms-2-output.txt` | `B4AE646E7E2234B311B39374C6A7CBF43424FF1059E59D25C55E7C8B60372D59` |
| `verification-section4-round3-axioms-3-input.lean` | `88DF5AD3BEC54BDFC5F93D3E34911E247338609B8098A2250E2933AA18EEB35A` |
| `verification-section4-round3-axioms-3-output.txt` | `D3D55C2F4F34DC3434B0510B8F7C498E5423238F0F677878F974F67880968687` |

| Final milestone | Unchanged weight | Accepted fraction | Contribution |
|---|---:|---:|---:|
| Source inventory | 10% | 1 | 10% |
| Forward 4.1–4.7 | 25% | 1 | 25% |
| Regularity and iteration 4.8–4.11, including analytical point initialisation | 35% | 0.75 | 26.25% |
| Dual subsection, including substantive unnumbered geometry | 20% | 0.75 | 15% |
| Integration and permitted-axiom audit | 10% | 1 | 10% |

The final total is **86.25%**, reported as **86% (80–92%)**, with moderately high confidence. These are the same fixed weights and allowed fractions used before the results. The increase from 80% is conservative: the annulus finishes the forward milestone, while the generic topological lemma and actual half-space atlas prevent completion of the regularity and dual milestones. The distance and inverse-display proofs close real analytical obligations even though the coarse fixed fractional scale does not separately award each one. The range reflects the remaining topology and atlas work within those fixed milestones, not probability of correctness.

**Stopping reason:** the four concrete obligations targeted in this round are now proved, independently reviewed and verified in the frozen batch. This review is complete for that scope and is frozen for packaging. Two distinct further tasks remain. Lemma 4.8 needs projection openness under its arbitrary topological-hypersurface input; the searched pinned library does not supply the invariance-of-domain step, and a conditional graph theorem is not a substitute. The dual-ball manifold package has a concrete route through actual half-space charts and chart coverage, but that atlas has not been implemented. It is the more direct next implementation task; a claim of C1 atlas compatibility would additionally require transition differentiability. Neither open item is classified as a false manuscript theorem.

No new counterexample to an original-hypothesis theorem or substantive manuscript proof defect was found. The earlier arbitrary-set weak-distance scope issue remains as previously recorded, and the withdrawn Section 3 Definition 3.9 objection remains withdrawn. Numerical pictures and trajectories remain outside deductive certification. The manuscript was not edited. This reviewer changed only this new review document. Any subsequent archive verification should be read-only to preserve the frozen review hash.
