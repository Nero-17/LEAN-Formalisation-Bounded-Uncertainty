# LEAN Formalisation of Bounded Uncertainty

Lean 4 formalisation of Section 3 of *Dynamics with state-dependent uncertainty: a boundary map approach*. The checked project contains 69 mathematical modules and 510 audited named declarations. Lean 4.28.0 and an exact mathlib revision are pinned below.

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

## Definition 3.9 and well-definedness in Proposition 3.10

The paper explicitly gives the formula before verifying its well-definedness. Proposition 3.10 supplies that verification under contraction. An earlier review overstated the failure of an unconditional extension as a refutation of the original definition requiring a correction to the paper. That interpretation has been withdrawn. The following example tests the role of the conditions; it does not contradict the definition and its subsequent well-definedness proof.

On the whole space, take f = id and ε(x) = 2 + sin(2x₁). The radius is positive, bounded, and smooth, and all closed balls remain in the whole space, so this is a valid two-dimensional system under Definition 3.1. At x = 0 the canonical gradient is (2,0). Choosing n = (0,1) makes the radicand negative. Lean's total real square root returns zero on nonpositive inputs, so the raw formula produces the normal (−2,0), outside the unit sphere. `exists_system_raw_exponential_not_unit` proves this failure for an actual system.

The implementation retains an unconditional real-valued raw formula and uses Proposition 3.10 to construct a typed sphere-valued map under contraction. `norm_normalUpdate_of_radicand_nonneg` also proves that pointwise nonnegativity of the radicand is enough for unit output. Theorem 3.17 states the bijectivity equivalence using a candidate formula independent of the contraction assumption, avoiding a circular definition or an unproved premise.

## Assumptions and correspondence with the paper

X may be nonconvex, f(X) may be nonclosed, and the radius may vanish. Contraction remains the pointwise condition that the gradient norm is strictly less than 1 at every point; it has not been replaced by a uniform global bound. Functions on the ambient space represent domain data. All derivatives come from genuine local extensions on open neighbourhoods, and their canonical values are proved independent of the extension. Neither `UniqueDiffOn X` nor smoothness of an arbitrary representative outside the domain is assumed.

`C1FrontierGraphAt` uses the local graph definition of a Euclidean C1 hypersurface, without prescribing a side of the set or a normal. Regular closedness and the frontier graph property imply local one-sidedness. Tietze extension is used only for topological straightening; local differentiation uses the original C1 graph function. Finite r and s are positive natural numbers. Infinite regularity uses a fixed `SmoothLocalExtensionAt` witness on the same underlying system: one function is C∞ on one open neighbourhood, rather than an unrelated family of finite-order extensions. Mixed-order conclusions apply directly to the same system.

SIRS uses the Euclidean norm on `EuclideanSpace ℝ (Fin 2)`. Its exact determinant is 171/200 + (57/200)S − (51/200)I and is at least 3/5. The gradient-norm supremum is κ/(20√2), attained at (1/2,1/2); the comparison 28.28 < 20√2 and the case κ = 3 are proved with exact arithmetic. Injectivity is established by an equivalent algebraic proof instead of following the paper's level-set argument. A triangle supplies the non-C1 invariant-set example; this is an analytical existence proof, not a numerical certification of the figures.

The paper's numerical plots, trajectories, and illustrated invariant boundaries do not come with exact numerical certificates for Lean to check. This project does not certify those images or formalise the dynamical theorems in Section 4 or later sections. The detailed scope, historical statuses, and independent review are recorded in [section3-coverage-review.md](section3-coverage-review.md).

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

The recorded full rebuild consisted of 16 modules completed serially and 53 compiled in parallel once their dependencies were ready. After the entry point compiled, all 510 independent axiom queries were checked by Lean in three groups. See [verification-build-procedure.md](verification-build-procedure.md) for the execution details. [verification.txt](verification.txt) contains the complete rebuild and axiom-audit output. [verification.json](verification.json) records module and supporting-file SHA-256 hashes, declaration and module counts, source line counts, toolchain versions, and scope. Every ZIP entry was also compared with its source file by SHA-256.

The 38-module-stage evidence is retained as `verification-38-module-batch.*`, and earlier evidence as `verification-previous-batch.*`. These files and the earlier semantic reviews preserve historical stages; the current coverage record is `section3-coverage-review.md`. Final acceptance used a full rebuild of all modules. Compilation does not replace independent semantic review. Subsequent documentation clarification and English translation preserve the checked Lean sources and compiler/audit logs; their metadata records the documentation updates separately from the original verification time.
