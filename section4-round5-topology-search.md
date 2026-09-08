# Section 4, round 5: topology foundation search and verified port

Research mode: **Bottleneck Research**, automatically selected because the general projection-openness step in Lemma 4.8 had persisted across several otherwise successful rounds. The assigned role was Agent 1: primary-source retrieval, route appraisal, and a concrete foundation probe. No user time or token limit was imposed. The requested effort was maximum for the critical proof route and high for retrieval; the persistent agent's effective setting could not be changed or read back and is not claimed to have been adjusted.

Search and verification window: **8–9 September 2026, Europe/London**, with this source assessment frozen at **9 September 2026, 00:09 BST**. Repository pages and branch labels are mutable; all imported code is identified below by immutable commits and SHA-256 hashes. This round began from the published **124-module, 811-declaration baseline, commit `bac3812`**. The fixed milestone weights and previously published estimate are historical inputs, not recomputed from this search.

## Outcome and claim ledger

A usable route was found and tested on the existing Lean 4.28.0/mathlib installation. The complete cubical-Sperner-to-Brouwer foundation now compiles as five isolated project modules. The parent agent separately ported the downstream invariance-of-domain proof, then supplied its Brouwer premise using this foundation. The blanket earlier assessment that no usable external foundation had been located is superseded by these concrete sources and compiler results.

| ID | Exact claim | Status and evidence |
| --- | --- | --- |
| R5-SEARCH-01 | The missing general dependency is openness of a continuous locally injective map from a boundaryless finite-dimensional topological manifold into its Euclidean model. | Mathematical dependency identified. An intrinsic chart alone does not provide an open projected image. |
| R5-SEARCH-02 | A dependency-closed invariance-of-domain proof from Brouwer exists in an open mathlib PR, independently of unfinished earlier experiments in that file. | Actual full source retrieved at commit `230d75a…`; the relevant slice was inspected and locally ported by the parent. |
| R5-SEARCH-03 | The MIT-licensed harfe source proves Brouwer for arbitrary nonempty compact convex subsets of finite-dimensional real normed spaces. | Five project modules compiled with Lean 4.28.0, exit 0, no warnings. Seven main transitive axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. |
| R5-SEARCH-04 | The combined project theorem proves open images of continuous injective maps on open finite-dimensional Euclidean domains without a fixed-point assumption. | Parent's `InvarianceOfDomain.lean` compiled, exit 0, no warnings; it explicitly discharges `BrouwerFixedPoint` using R5-SEARCH-03. |
| R5-SEARCH-05 | The same foundation supplies openness of an injective restriction of a continuous map from an actual `ChartedSpace E M` into `E`. | Parent's compiled `isOpenMap_restrict_of_continuous_injOn` retains the original topology on `M`. No graph or local-separation assumption is added. |
| R5-SEARCH-06 | The other inspected projects do not provide a cheaper verified replacement for this route. | Comparative assessment of actual files, described below. This is a ranked engineering judgment, not a proof that no other formalization exists. |

This report does **not** independently certify that every final wrapper for the manuscript's Lemma 4.8 has been integrated or that the full repository audit has completed. Those are separate parent/Agent 2 integration tasks. The foundation that previously obstructed them is now a proved local dependency rather than an assumed theorem.

## Exact logical obstacle and the new dependency chain

The manuscript assumes that the hypersurface is a topological manifold in its subspace topology. It does not assume an ambient flattening chart. The two-moving-point secant condition makes the adapted projection locally injective and gives a Lipschitz inverse over its image. That proves a graph over a subset of the horizontal space. The remaining issue was proving that the subset is open.

For an intrinsic manifold chart, composition of its inverse with the projected map is a continuous injective map between open subsets of Euclidean spaces of the same dimension. Invariance of domain makes its image open. It therefore supplies exactly the missing premise, including for arbitrary topological hypersurfaces. The earlier regular-closed-frontier cap argument still proves its own valid specialization, but is not used to disguise the general topological dependency.

The verified route is:

1. A concretely defined finite cubical grid and its simplices satisfy the required face-counting identities.
2. Parity and dimension induction give a fully labeled simplex.
3. Labels constructed from a continuous cube self-map give arbitrarily close points with opposite coordinate inequalities.
4. Compact subsequence extraction and continuity give a fixed point of that map.
5. An affine-span reduction and genuine homeomorphisms transport the result to any nonempty compact convex set in finite dimension.
6. Brouwer's property gives stability of a zero. A continuous inverse on a compact embedded ball extends by Tietze; polynomial approximation and the measure-zero image of a sphere produce the contradiction needed for invariance of domain.
7. Intrinsic charts transport Euclidean open-image invariance to the actual manifold projection.

No sphere-homology computation, assumed no-retraction theorem, or new axiom appears in this chosen chain.

## Ranked routes and actual evidence

### 1. Cubical Sperner plus the Brouwer-to-domain PR: selected and compiled

The decisive new primary source was [mathlib PR 36770](https://github.com/leanprover-community/mathlib4/pull/36770), entitled “feat: invariance of domain via Brouwer's fixed point theorem.” The GitHub API returned an open PR with head repository `Xmask19/mathlib4`, branch `invariance_of_domain`, and head commit **`230d75acb32d80e7d7c4f4cd028b139f3dc28be7`**. Its actual toolchain is Lean **4.32.0-rc1**. The full 1,573-line `Mathlib/AlgebraicTopology/InvarianceOfDomain.lean` was downloaded, not inferred from the title or search snippet.

The original file is not a complete stand-alone proof of both foundational theorems: it contains unfinished earlier retraction experiments, with placeholders at original lines 153 and 1007–1009. The usable dependency slice consists of:

- `differentiable_approx_of_continuous`, original lines 1014–1113;
- the explicit Brouwer interface corresponding to the upstream class near line 109;
- `stability_of_zero`, starting at line 1120;
- `invariance_of_domain_interior`, starting at line 1142;
- `invariance_of_domain_open_map`, lines 1406–1438.

The downstream slice contains no placeholder and does not use the unfinished experiments. The parent port makes the Brouwer premise an explicit `BrouwerFixedPoint E` structure argument, rather than an unproved registered instance. The zero-dimensional branch is handled explicitly by showing that the image is all of the subsingleton space; the approximation proof's nontriviality requirement is used only in the other branch. This records a genuine coverage detail, not a positive-dimensional restriction on the final result.

The primary mathematical exposition is [Terence Tao's 2011 proof](https://terrytao.wordpress.com/2011/06/13/brouwers-fixed-point-and-invariance-of-domain-theorems-and-hilberts-fifth-problem/). The actual Lean proof uses compactness, Tietze extension, differentiable approximation, and a measure-zero sphere-image argument. This is an inference from reading the implementation as well as its own attribution, not a claim that the blog supplies a Lean artifact.

The Brouwer premise is discharged by [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838), immutable commit **`770940ddf9878cf61952ed53d910b92bca841838`**. All five required source files were downloaded and inspected. Their combined source is approximately 84 KB. The current README and actual toolchain did not agree during retrieval: the README described an older version, while the fetched `lean-toolchain` specified **Lean 4.32.0**. The actual file controls this report.

A Lean 4.27 snapshot, commit **`7c9944876b54a7d5fcdbd542f56385b33c0d2e90`**, was retrieved as a compatibility lead. Its preparation and main combinatorial files compiled on pinned 4.28 with only linter/deprecation warnings. However, the current MIT-licensed files also compiled and needed only one finite-set membership simplification in the main combinatorial file. The historical snapshot was consequently not copied into the project.

The current MIT license was added at the selected current commit. The imported source is exactly that licensed version, with attribution, namespace/import isolation, and one documented proof-expression adjustment. [Third-party provenance](third-party/README.md) records the five raw hashes and the exact patch. The complete MIT and Apache 2.0 licenses are retained there. No permission was inferred from the absence of an old license file.

### 2. Lean 3 sphere homology and no-retraction: real proof, larger migration

The full decisive sources from [Shamrock-Frost/BrouwerFixedPoint](https://github.com/Shamrock-Frost/BrouwerFixedPoint/tree/2883ceb0f5d461155fa1689266a7af40ff8ae671) were retrieved at commit **`2883ceb0f5d461155fa1689266a7af40ff8ae671`**. Its `leanpkg.toml` fixes **Lean 3.51.1** and old mathlib revision `13361559d66b84f80b6d5a1c4a26aa5054766725`.

The 16 KB `src/brouwer_fixed_point.lean` contains an actual ball-to-sphere no-retraction argument and a compact-convex Brouwer theorem. It imports the 114 KB `homology_of_spheres.lean`, which in turn imports custom homology, barycentric subdivision, reduced homology, and convex-space developments. Its no-retraction proof applies the singular-homology functor and contrasts the homology of a contractible ball with the nonzero homology of a sphere.

No placeholder was found in these two retrieved decisive files. The complete dependency closure was not ported or compiled in this campaign, so this report does not certify its current Lean 4 compatibility. Moving it to the pinned project would require a Lean 3-to-4 migration plus reconciliation of substantial custom categorical and topological infrastructure. The already compiled cubical route has much lower demonstrated transfer cost.

### 3. Another Lean 4 Sperner project: useful combinatorics, advertised Brouwer still axiomatic

The closed [lean-genius issue 7966](https://github.com/rjwalters/lean-genius/issues/7966) led to merged [PR 8576](https://github.com/rjwalters/lean-genius/pull/8576). Actual API retrieval showed that this PR adds **one** 521-line file, `proofs/Proofs/SpernerNDimMathlib.lean`, at commit **`596b14c65f81197b502c38fe125d1fbd7c83d9e3`**.

That file proves a parity theorem for an abstract `CellComplex` whose structure fields specify adjacency, symmetric matching, and matching facet vertices. It is not by itself a construction of arbitrarily fine Euclidean triangulations or a continuous fixed-point theorem. The `BrouwerFixedPoint.lean` at the same immutable commit was also retrieved: it explicitly declares `no_retraction_axiom` at line 124 and `retraction_construction` at line 178, and its advertised Brouwer theorem uses them. The merged/closed status therefore did not establish the required axiom-free foundation. This route was not adopted.

### 4. Isabelle/HOL Kuhn–Brouwer: complete alternative in another prover

Agent 3 independently identified and opened the full primary [Isabelle `Brouwer_Fixpoint` theory](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Brouwer_Fixpoint.html); Agent 1 then opened the same complete theory. It attributes John Harrison and translators, explains its Kuhn combinatorial approach, and contains actual proofs of cube/ball/general Brouwer and no-retraction results.

This confirms a concrete alternative proof architecture that avoids sphere homology. It is not a callable Lean theorem. Porting the theory and its HOL library dependencies would be substantial work; the selected Lean cubical proof realizes the same useful avoidance of homological infrastructure within the pinned prover. No Isabelle proof was imported or counted as Lean-verified work.

### 5. Pinned/upstream Borsuk–Ulam, degree, and homology interfaces: no shorter callable result located

The pinned algebraic-topology, topology, and manifold source areas were checked for invariance-of-domain, Borsuk–Ulam, Brouwer, no-retraction, sphere-degree, and sphere-homology names. The relevant pinned manifold file `Geometry/Manifold/IsManifold/InteriorBoundary.lean` explicitly notes that certain chart-independence/interior-openness statements require additional topology such as sphere homology. This is supporting evidence for the previously observed local gap, not evidence that no external code exists.

GitHub primary issue/PR searches included exact Borsuk and no-retraction phrases and a sphere/homology combination. The first two returned no matching mathlib records in this search; the third was noisy and returned many unrelated records. Those negative searches are weak evidence and are not used as an exhaustiveness claim. More importantly, an invariance-of-domain issue search found PR 36770, even while [theorem request 33018](https://github.com/leanprover-community/mathlib4/issues/33018) remained open. The open request alone would have missed the usable branch.

## Concrete probe and project verification

All raw downloads and initial compiler output were kept outside the project in `work/section4-round5-topology-sources/`. The immutable downloaded files were not edited. A separate `harfe-port-4.28/` directory held the compatibility probe. The compiler used was the existing Lean 4.28.0 binary, and `LEAN_PATH` contained only the isolated probe build plus the existing pinned packages' build paths. The fixed mathlib revision remained **`8f9d9cff6bd728b17a24e163c9402775d9e6a365`**.

The first current-version probe accepted `cubical_sperner_prep.lean` and `convex_homeos.lean` unchanged. `cubical_sperner.lean` failed at one proof term because the older simplifier had already reduced a membership goal to its predicate. Removing the now-redundant membership constructors resolved that error. The main combinatorial, application, and Brouwer modules then all compiled, exit 0, no warnings. This was a source-compatibility repair, not a weakened theorem.

The project copies are:

| Module | SHA-256 of compiled source |
| --- | --- |
| `VendorSpernerPrep` | `F09FA2C60393DB712F97C04A362C137693B6D06DABDC5B763BCF33A2B83AEE4C` |
| `VendorSperner` | `AC3234F82109A1BA13AC900CE062521DC0860BC026F7D1886F5180398BB8B88A` |
| `VendorSpernerApplication` | `766E62AF3DEC55EA14F0287CCE7C2B646DA80298249C290391ED60BA96804DC4` |
| `VendorConvexHomeomorphisms` | `6BE8FE2F79137C4800F5127F960AC87851B111A0AE1325C8A936C88D1407951B` |
| `VendorBrouwer` | `09BC6E30E25318154BAB45FAC1975BB112AB8E8DCA487795D212F36F9EBD5DBA` |

They compiled together through the existing individual-module command:

```powershell
& 'outputs/bounded-uncertainty-lean/scripts/Check.ps1' -Modules VendorSpernerPrep,VendorSperner,VendorSpernerApplication,VendorConvexHomeomorphisms,VendorBrouwer
```

The log is `work/section4-round5-topology-sources/vendor-project-compile.log`. The separate `VendorBrouwerAxiomAudit.lean` printed transitive axioms for `strong_cubical_sperner`, `weaker_cubical_sperner`, `fixed_point_unit_cube`, `homeo_unit_cube_of_convex_compact`, `brouwer_fixed_point`, `brouwer_fixed_point_isFixedPt`, and `brouwer_fixedPoints_nonempty`. Every result was exactly the permitted set `propext`, `Classical.choice`, `Quot.sound`; the audit process exited 0. Its log is `vendor-axiom-audit.log` in the same directory.

Agent 3 independently compared all five project files with the licensed original, reconciled their hashes and the exact patch, inspected the cube compactness/limit proof and affine-span reduction, and accepted their mathematical scope at the individual-compilation level. The parent retains responsibility for the integrated all-declaration audit, including the named finite-type instance and all vendor helper declarations. Nested namespaces and the instance must be inventoried honestly rather than hidden to satisfy an old parser.

The parent supplied clean compilation results for `InvarianceOfDomainFromBrouwer.lean` and `InvarianceOfDomain.lean`. At this report's cutoff their source hashes were respectively `61A2DA2B33B9315568CE22934EBD58E85B17A5B176DAF02A55E47578C80F17D0` and `D4D65E3BD86B25D4E4E1C72901306779590C776F56D101331C5B4736CA1FE7B2`. Agent 1 read the explicit discharge and chart-openness signatures; their proof development belongs to the parent.

## Source log and stopping criterion

The local source archive contains the complete original IOD file, both selected current and historical harfe snapshots, the decisive Lean 3 files and toolchain, and the actual alternate Sperner/Brouwer files from PR 8576's commit. `source-sha256.json` records raw Lean-source hashes; the PR metadata/file-list JSON for 8576 records the exact closed-issue follow-up. Public GitHub API and raw-content requests were read-only; no repository or paper was written through those services.

Primary retrieval endpoints included the GitHub issue-search API, PR 36770 metadata/file list, immutable raw IOD source and license, harfe's recursive trees and `lean-toolchain`/license commit histories, PR 8576 metadata/file list, and the two complete mathematical exposition/proof pages linked above. A failed historical `LICENSE` download was resolved by inspecting the tree and license history; it was not silently treated as permission. All successful import provenance comes from the current licensed commit.

The campaign stops because a concrete route survived pinned-version compilation, actual dependency inspection, and a transitive axiom check. Continuing broad searches for a different foundation would no longer address the active bottleneck efficiently. The remaining work is the transparent integration of the now-proved chart-openness interface into the original hypersurface criterion and the final repository audit. No dependency upgrade, extra axiom, stronger graph premise, or assumed separation theorem is needed by this route.
