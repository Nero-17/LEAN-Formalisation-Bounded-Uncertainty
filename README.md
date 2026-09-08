# LEAN Formalisation of Bounded Uncertainty

Lean 4 formalisation of Section 3 and selected results of Section 4 of *Dynamics with state-dependent uncertainty: a boundary map approach*. The current project contains 124 mathematical modules and 811 named declarations. Lean 4.28.0 and an exact mathlib revision are pinned below. Section 3 is complete within the stated deductive scope; Section 4 is in progress.

The project covers the deductive content of Section 3 in the fixed paper snapshot: definitions and interfaces, all lemmas, propositions and theorems, analytical examples, and counterexamples discussed in the remarks. Definition 3.9 introduces a formula, and Proposition 3.10 then proves its well-definedness under contraction; the formalisation represents these together. The additional `DefinitionScope` example shows that an unconditional extension of the construction can fail. It does not refute the definition or proposition in their stated context. Numerical figures are not treated as proved dynamical conclusions.

The paper snapshot is commit `3200c88826c73210d1e83bfc46de1656ee0788ef`; Section 3 occupies lines 581–1857 of its original `main.tex`. The toolchain is Lean 4.28.0, with mathlib pinned to `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

| Paper content | Formalised result | Main modules |
|---|---|---|
| Definition 3.1 and Notation 3.2 | Systems, genuine local extensions, and independence of the canonical derivative and gradient from extension choices on regular closed domains; finite orders, a fixed-neighbourhood C∞ interface, and mixed orders | Basic, AmbientDerivative, CanonicalDerivative, BoundaryMap, SmoothLocalExtension, MixedRegularity |
| Notation 3.3 | Compactness and regular closedness of f(A), frontier(f(A)) = f(frontier A); actual contributing and uniquely contributing pairs; inward and outward normal pairs and bundles, independent of charts | DiffeomorphismSetGeometry, Section3Interfaces, NormalBundleNotation |
| Lemma 3.4 | Exclusion of interior contributors; contributor existence for compact centre sets and the full boundary inclusion, connected to the actual setValuedImage | BoundaryContributors, InflationGeometry |
| Lemmas 3.5–3.7 and Theorem 3.8 | Local one-sidedness from an unoriented C1 frontier graph and regular closedness, followed by actual outward normals; common normals, tangent balls, contact gradients, signed multipliers, the actual exponential map, and explicit position formulas, including zero radius | C1FrontierTopology, C1FrontierGraph, C1FrontierContact, LocalBoundary, SphereBoundary, ContactGeometry, ContributorFormula |
| Definition 3.9 and Proposition 3.10 | The raw exponential formula and its well-definedness and continuity as a sphere-valued map under contraction; an additional counterexample to its unconditional extension | NormalFormula, ExponentialMap, BoundaryMap, DefinitionScope |
| Definition 3.11 and Remark 3.12 | Inverse transpose, L, E, and β constructed from the actual differential; constancy of the radius on X alone implies a zero canonical gradient and the classical formula | InverseTranspose, LinearLiftHomeomorph, ConstantRadius |
| Example 3.13 | The original SIRS polynomial map and state simplex; actual derivative and determinant, injectivity, and a genuine C∞ inverse; the exact gradient and attained norm supremum; the radius bound by boundary distance and ball invariance; an actual system with smooth β | SIRSAlgebra, SIRSGeometry, SIRSGradient, SIRSDeterministic, CompactSmoothInverse, SIRSInvariance, SIRSSystem, SIRSSmooth |
| Theorem 3.14: topology | β is a homeomorphism onto its actual image; when f(X) = X, it is a homeomorphism of the full state bundle onto itself | RayMonotonicity, ExponentialInjectivity, ExponentialEmbedding, SelfSurjectivity, BoundaryHomeomorph |
| Theorem 3.14: regularity | The actual β and its inverse on the actual image have local C^(min(r,s)−1) extensions; all finite positive orders, both orders infinite, and either mixed finite/infinite case are covered; neighbourhood extensions genuinely take values in the sphere | HigherDerivative, HigherExponential, HigherLinearLift, HigherLinearInverse, HigherBoundaryMap, ImplicitRadius, HigherExponentialInverse, HigherBoundaryInverse, SmoothBoundaryForward, SmoothImplicitRadius, SmoothExponentialInverse, SmoothBoundaryInverse, MixedRegularity, BundleSphereExtension, SmoothSphereExtension |
| Theorem 3.14: nonsingular differential | Bundle tangent spaces E × n⊥ of dimension 2d−1; independence of the restricted differential from extension choices; at sufficient differentiability orders, an actual continuous linear equivalence E × n⊥ ≃ E × u⊥ | BundleTangent, BundleDifferential, BoundaryDifferential, SmoothBoundaryInverse, MixedRegularity |
| Proposition 3.15 and Remark 3.16 | An interior or whole-space zero-radius point has zero gradient and is fixed by E; an actual contracting two-dimensional SIRS system changes the normal at a boundary zero-radius point; a nonnegative radicand suffices for unit output | ZeroRadius, DegenerateNormal, SIRSSystem |
| Theorem 3.17 | When f(X) = X, the candidate β formula, defined without a contraction parameter, gives a full-bundle bijection if and only if the actual radius satisfies pointwise contraction | ContractionNecessity, ContractionCharacterization |
| Remark 3.18 | In one dimension the unit directions are ±1 and the radicand is 1; X = [−1,1], f = id, and ε(x) = (1−x²)/2 satisfy every other system assumption while the actual β remains bijective without strict contraction | OneDimensionalCounterexample, OneDimensionalSystem |
| Motivation involving a non-C1 invariant set | An actual two-dimensional identity system with zero radius has a boundary-map homeomorphism, while a vertex of a compact regular closed invariant triangle admits no C1 frontier chart | NonsmoothInvariantSet |

## Section 4 progress

The fourth Section 4 batch adds 6 modules and 28 declarations, preserving all 118 previously verified mathematical source files. The current claim ledger and independent review are in [section4-round4-review.md](section4-round4-review.md). Earlier [round-three](section4-round3-review.md), [round-two](section4-round2-review.md) and [first-batch](section4-coverage-review.md) reviews preserve their historical assessments.

| Paper content | Formalised result | Main modules |
|---|---|---|
| Assumption 4.1 and Lemmas 4.2–4.4 | Exact source visibility; actual contributor existence; unique recipient from source C1 alone; unique contributor from recipient C1 alone; no nonconstant arc in one constituent sphere | SourceVisibility, RecipientUniqueness, ContributorUniqueness, ForwardNormalBundle |
| Lemma 4.5 and Theorem 4.6 | Derivation of the image boundary and inverse-transpose normal from actual local diffeomorphism data; actual beta transports contact normal pairs; equality of outward bundles and bijectivity of the projected boundary map | DiffeomorphismBoundaryNormal, ForwardBoundaryCorrespondence, ForwardNormalBundle |
| Corollary 4.7 | Invariant outward bundle, actual restricted homeomorphism and inverse, finite and fixed-C-infinity sphere-valued local extensions, and nonsingular differential on the ambient state bundle | InvariantBoundaryRegularity, InvariantBoundaryExtensions |
| Theorem 4.9 | Full C1 frontier graph equivalence with actual Gamma injectivity under source visibility; actual positive/zero-radius two-moving-point secants; constructed normal coordinates, open graph projection and continuous derivative | RecipientParametrization, RecipientSecants, RecipientRegularity, SequentialFrontierCriterion, FrontierNormalCriterion, BoundaryDefiningGraph |
| Theorem 4.10 | Full iterated boundary inclusion, in both typed and original ambient normal-bundle notation, with no smooth intermediate boundaries or source visibility and with zero radii permitted | SetValuedIterates, MaximizerGeometry, MaximizerTransport, MaximizerIteration, IteratedBoundaryInclusion |
| Proposition 4.11 and Example 4.12 initialization | The actual fixed-source fibre maps onto the actual noise-ball outward normal bundle; the singleton first image and its boundary projection are identified | BoundaryFibre |
| Definition 4.13 and Lemmas 4.14–4.15 | Actual dual balls, union-defined dual inflation and membership-reversing dual maps; pointwise/setwise preimage factorisations; distance description for nonempty compact or closed sets; a counterexample to the explicitly arbitrary-set distance equality | DualInflation, DualInflationScope |
| Dual-ball and dual-inflation geometry | Compactness, star-convexity, regular closedness, actual C1 frontier and one-sided graphs; compact-input dual-inflation geometry including empty input | DualBallGeometry, DualInflationGeometry, DualBoundaryInterfaces |
| Theorem 4.16 | Actual exponential image equality of inward normal bundles from two-sided attained nearest points; uniqueness is unnecessary for this proof | DualBoundaryContact, DualBoundaryCorrespondence |
| Theorem 4.17 | Actual inverse-beta image equality; genuine preimage defining data, regular closedness and fixed-model frontier charts are constructed | WholeSpaceNormalTransport, DualInverseBoundary, DualBoundaryInterfaces |
| Corollary 4.18 | Actual invariant inward bundle, restriction homeomorphism, finite/smooth sphere-valued local extensions and ambient state-bundle nonsingular differential | DualInvariantBoundary |

| Annulus visibility example | Actual compact regular closed C1 annulus with identity map and radius one; exact inflation is the radius-three ball; all inner-boundary balls lie in its interior, so source visibility fails | AnnulusVisibility |
| Point-start iteration | Every positive singleton-iterate frontier is contained in the projection of the corresponding actual beta iterate of the initial full unit fibre | PointStartIteration |
| Unique-nearest-point distance differential | Actual distance and squared-distance gradients; uniqueness only at the marked point; compact scope and closed/proper extension, without convexity | NearestPointContinuity, DistanceDifferentiability, ClosedDistanceDifferentiability |
| Inverse exponential display after 4.16 | Proved unit-bundle bijection, genuine inverse, and inverse inward-normal-bundle equality with dual regular closedness derived | DualExponentialInverse |

| Dual-ball manifold with boundary | Actual half-space charts on the existing dual-ball subtype topology, covering interior and boundary points; standard ambient-dimensional EuclideanHalfSpace model; compactness, Hausdorffness, second countability, topological manifold structure and separate C1 frontier | RelativeHomeomorph, BoundaryAtlas, HalfSpaceModel, ChartedSpaceModelTransport, DualBallManifold |
| Lemma 4.8, analytical first step | Original distinct-endpoint sequence condition gives uniform all-pair bounds, little-o chords and local orthogonal-projection injectivity; no projection openness is claimed | DistinctSecants |


**Still open:** standalone Lemma 4.8 for an arbitrary topological hypersurface, specifically its topological projection-openness step. The dual-ball manifold-with-boundary structure is now proved. Numerical trajectories are not certified. Section 4 is not claimed complete.

The dual-ball atlas retains the actual subspace topology. Boundary charts flatten a genuine one-sided graph and use its continuous extension only on a neighbourhood of agreement; interior charts shift the first coordinate into the positive half-space. Actual relative open partial homeomorphisms and their inverse laws supply chart coverage. A proved model homeomorphism gives the standard d-dimensional EuclideanHalfSpace. The manifold statement is topological (IsManifold at order zero), with the separately proved C1 frontier; differentiable atlas transitions are not asserted.

For standalone 4.8, distinct bad pairs at radii tending to zero prove the uniform chord estimate; a one-half estimate forces equal projected points to coincide. The remaining openness is genuinely topological: for an arbitrary manifold subset of a fixed hyperplane the normal secants already vanish identically, so the analytical hypothesis alone does not supply the needed local openness. No stronger ambient-flatness hypothesis has been substituted.

The separately stated distance derivative is now proved: compactness and uniqueness at the base point force every nearby minimizer to approach that point; a two-sided squared-distance remainder estimate yields the derivative, and a square-root argument yields the distance gradient. A proved local compact truncation extends this to closed sets in proper spaces. The alternative normal-contact proof of 4.16 is retained. The point-start result asserts inclusion for later iterates, not equality without further visibility assumptions.

Theorem 4.9 now has a complete proof under the original graph and visibility hypotheses, with zero radius permitted. The local projection is proved open using regular closedness, connected caps and unique vertical crossings, and the resulting graph is proved C1. This actual-frontier route does not prove standalone Lemma 4.8 for arbitrary topological manifolds. At zero radius a quantitative small/large-radius estimate replaces the manuscript's subsequence split. For 4.16, tangent dual-ball and exterior-ball normal comparisons replace distance differentiation and show that nearest-point attainment suffices. These are alternative verified proofs; the Overleaf manuscript was not edited.

Theorem 4.10 uses an alternative final proof. The paper's maximizing-gradient induction is strengthened to local maxima and proved using genuine local representatives. The projection of the iterated initial normal bundle is compact. Exterior points approaching an image-boundary point have nearest points that maximize a smooth negative squared-distance function with nonzero gradient. The induction puts these nearest points in that projection, and closedness gives the desired inclusion. This preserves the theorem's original hypotheses; no manuscript proof has been edited.

The arbitrary-set weak-distance equality in 4.13/4.15 has a genuine scope failure. In an actual whole-plane identity system with constant radius one, take the open unit ball A and y twice a unit vector. Then infDist(y,A) = 1, but dist(y,x) > 1 for every x in A, so y belongs to the weak distance sublevel and not to the union-defined dual inflation. The union/preimage identities remain valid for arbitrary A, and the nonempty compact/closed distance identities are proved. This does not refute the later compact-set dual theorems. The empty-set totalisation of Lean's real infDist is recorded separately.

## Definition 3.9 and well-definedness in Proposition 3.10

The paper explicitly gives the formula before verifying its well-definedness. Proposition 3.10 supplies that verification under contraction. An earlier review overstated the failure of an unconditional extension as a refutation of the original definition requiring a correction to the paper. That interpretation has been withdrawn. The following example tests the role of the conditions; it does not contradict the definition and its subsequent well-definedness proof.

On the whole space, take f = id and ε(x) = 2 + sin(2x₁). The radius is positive, bounded, and smooth, and all closed balls remain in the whole space, so this is a valid two-dimensional system under Definition 3.1. At x = 0 the canonical gradient is (2,0). Choosing n = (0,1) makes the radicand negative. Lean's total real square root returns zero on nonpositive inputs, so the raw formula produces the normal (−2,0), outside the unit sphere. `exists_system_raw_exponential_not_unit` proves this failure for an actual system.

The implementation retains an unconditional real-valued raw formula and uses Proposition 3.10 to construct a typed sphere-valued map under contraction. `norm_normalUpdate_of_radicand_nonneg` also proves that pointwise nonnegativity of the radicand is enough for unit output. Theorem 3.17 states the bijectivity equivalence using a candidate formula independent of the contraction assumption, avoiding a circular definition or an unproved premise.

## Assumptions and correspondence with the paper

X may be nonconvex, f(X) may be nonclosed, and the radius may vanish. Contraction remains the pointwise condition that the gradient norm is strictly less than 1 at every point; it has not been replaced by a uniform global bound. Functions on the ambient space represent domain data. All derivatives come from genuine local extensions on open neighbourhoods, and their canonical values are proved independent of the extension. Neither `UniqueDiffOn X` nor smoothness of an arbitrary representative outside the domain is assumed.

`C1FrontierGraphAt` uses the local graph definition of a Euclidean C1 hypersurface, without prescribing a side of the set or a normal. Regular closedness and the frontier graph property imply local one-sidedness. Tietze extension is used only for topological straightening; local differentiation uses the original C1 graph function. Finite r and s are positive natural numbers. Infinite regularity uses a fixed `SmoothLocalExtensionAt` witness on the same underlying system: one function is C∞ on one open neighbourhood, rather than an unrelated family of finite-order extensions. Mixed-order conclusions apply directly to the same system.

SIRS uses the Euclidean norm on `EuclideanSpace ℝ (Fin 2)`. Its exact determinant is 171/200 + (57/200)S − (51/200)I and is at least 3/5. The gradient-norm supremum is κ/(20√2), attained at (1/2,1/2); the comparison 28.28 < 20√2 and the case κ = 3 are proved with exact arithmetic. Injectivity is established by an equivalent algebraic proof instead of following the paper's level-set argument. A triangle supplies the non-C1 invariant-set example; this is an analytical existence proof, not a numerical certification of the figures.

The paper's numerical plots, trajectories, and illustrated invariant boundaries do not come with exact numerical certificates for Lean to check. This project does not certify those images. The Section 3 scope and historical review are recorded in [section3-coverage-review.md](section3-coverage-review.md); the Section 4 table above and its separate review distinguish completed results from remaining obligations.

## Build and axiom audit

With Lean/Lake installed, run these commands from the project directory:

~~~text
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
~~~

The original Windows verification environment can also run:

~~~powershell
.\scripts\Check.ps1 -Audit
~~~

That script recompiles every module in entry-point dependency order, compiles the entry point, and runs `AxiomAudit.lean`. Its defaults record the original machine's toolchain and dependency cache; use the `LeanExe` and `DependencyRoot` parameters for other installations. Build output is confined to the project's `.lake/build` directory.

`AxiomAudit.lean` explicitly audits every handwritten named definition, theorem, lemma, and structure. Generated declarations are checked transitively through their dependencies. Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted. The project uses no `sorry`, `admit`, additional unproved axioms, `unsafe`, or `native_decide`.

The preserved Section 3 full rebuild consisted of 16 modules completed serially and 53 compiled in parallel once their dependencies were ready, followed by 510 axiom queries in three groups. [verification-build-procedure.md](verification-build-procedure.md), [verification.txt](verification.txt), and [verification-section3.json](verification-section3.json) preserve that baseline evidence.

The current Section 4 round uses incremental verification: hash-check all 118 unchanged baseline sources, freshly rebuild all 6 additions in dependency order, compile the updated root, and run all 811 current axiom queries in three disjoint groups. [scripts/VerifySection4Round4.py](scripts/VerifySection4Round4.py) checks exact source-to-audit name coverage. Baseline objects are reused; this is not a fresh rebuild of all 124 modules. See [verification-section4-round4-procedure.md](verification-section4-round4-procedure.md), [verification-section4-round4.txt](verification-section4-round4.txt), and [verification.json](verification.json). Historical evidence remains intact. Standard Lake commands still build the entire project from source.

The 38-module-stage evidence is retained as `verification-38-module-batch.*`, and earlier evidence as `verification-previous-batch.*`. These files and the earlier semantic reviews preserve historical stages. Section 3 acceptance used a full rebuild of its 69 modules; later documentation clarification and English translation preserved those checked sources and logs. Section 4 adds new modules and separate verification evidence. Compilation does not replace independent semantic review.
