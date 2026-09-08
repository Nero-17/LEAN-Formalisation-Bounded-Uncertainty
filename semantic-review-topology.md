# Section 3 Lean Formalization: Semantic and Assumption Review

> **Historical scope:** This is the review from the 20-module stage. Its pending-work statements describe that stage, not the current implementation. For current coverage, see [section3-coverage-review.md](section3-coverage-review.md).

Date: 2026-09-08. Reviewer: `lean_normal_algebra`.

The review covers the source in `outputs/bounded-uncertainty-lean/BoundedUncertainty` at that stage. The paper baseline is `work/fundamental-audit-20260907/online-3200c88/main.tex`, particularly Definition 3.1, the local ambient-extension convention, Theorem 3.14, Proposition 3.15, and Theorem 3.17.

**Conclusion: Within the mathematical scope checked below, no strengthened assumptions, circular definitions, substitution of an incorrect gradient representative for the paper's gradient, or reliance on closedness of a potentially nonclosed image were found. The topological conclusion of Theorem 3.14 and the equivalence in Theorem 3.17 have faithful formalized semantics.** This is not a statement that every theorem in Section 3 has been completed, and it does not replace final Lean compilation and an audit of axiom dependencies.

## Independence and Review Scope

This agent independently read and reviewed the following modules written by other authors: `Basic`, `AmbientDerivative`, `CanonicalDerivative`, `InverseTranspose`, `LinearLift`, `VaryingLinearLift`, `BoundaryMap`, `BoundaryContinuity`, `LinearLiftHomeomorph`, `RayMonotonicity`, `ExponentialEmbedding`, `SelfSurjectivity`, `ContractionNecessity`, and `ContractionCharacterization`.

This agent contributed to `NormalFormula`, `ExponentialMap`, `ZeroRadius`, `ExponentialInjectivity`, `BoundaryInjectivity`, and `BoundaryHomeomorph`. These files may be listed as implementation work, but **this report's reading of them must not be counted as independent verification**. The lead agent has separately and explicitly reviewed the restrictions, compositions, actual-range packaging, and full-image branch in `BoundaryHomeomorph`. Independent acceptance of this agent's other modules and the project-wide axiom audit remain coordinated by the lead agent.

## Correspondence Between Original and Formalized Assumptions

| Paper condition | Representation at this stage and review finding |
| --- | --- |
| Finite-dimensional Euclidean space of dimension at least 2 | `2 ≤ Module.finrank ℝ E` in a real inner product space. When finite dimensionality is needed, the instance is derived from positive finrank; finite-dimensional compactness is not used as an undeclared assumption. The coordinate-free formulation includes the original Euclidean setting. |
| `X` is regular closed | Expressed exactly as `closure (interior X) = X`; closedness is derived. `X` is not required to be convex, bounded, compact, or without boundary. |
| `f : X → f(X) ⊆ X` is a diffeomorphism under the paper's convention | An explicit inverse, inverse maps-to property, left inverse, local extensions in both directions, and an invertible forward differential. The right inverse and injectivity follow from these fields. `f(X)=X` is not part of the basic system. |
| The radius is nonnegative and has a uniform finite upper bound | `radius_nonneg`, `radius_le_bound`, and a positive `radius_bound`. There is no positive lower bound; zero radius is retained. |
| `F(X) ⊆ X` | `closedBall (map x) (radius (map x)) ⊆ domain`; the radius is indeed evaluated at `f(x)`. |
| Smoothness requires only an ambient extension near each point | `LocalExtensionAt` records an open neighborhood, local `ContDiffOn`, and equality on `X ∩ neighborhood`. The ambient representative is not required to be smooth outside the domain. |
| Pointwise contraction | For every `y : domain`, `‖radiusGradient y‖ < 1`. This is not replaced by `sup ‖gradient‖ < 1`. |
| Image and inverse in the main theorem | The range packaging uses the actual `Set.range (boundaryMap hcontraction)` with the subspace topology; closedness of the image is not assumed. Only the full-image branch explicitly requires `map '' domain = domain`. |

At this stage, `r,s` are encoded as finite positive integers. What has been completed is the topological conclusion; higher local regularity of class `C^(min(r,s)-1)` has not been packaged into a Homeomorph and claimed as proved.

## Independent Evidence and Decisions

### R1 — Compatibility of Derivatives of Local Extensions: ACCEPT

`AmbientDerivative.eqOn_fderiv_of_contDiffOn_eqOn` first obtains equality of derivatives on `interior X ∩ U` from local equality of the functions, then extends that equality to `X ∩ U` using continuity of both derivatives. The argument actually uses `X ⊆ closure (interior X)` and openness of `U`, which suffice for the required local density.

`fderiv_eq_of_local_ambient_extensions` restricts two different neighborhoods to their intersection, without requiring a single globally smooth extension. Consequently, `CanonicalDerivative.ambientDerivative_eq_extension` proves that the derivative selected by choice agrees with the derivative of every valid local extension. Continuity of the canonical derivative is likewise obtained using one neighborhood at each point.

This step avoids two incorrect shortcuts: directly differentiating an ambient representative that is arbitrary outside the domain, and adding `UniqueDiffWithinAt` for the original set without proof.

### R2 — Actual Gradient, Differential, and Inverse Transpose: ACCEPT

`BoundaryMap.radiusGradient` is the vector obtained by applying the inverse of the real inner product space's Riesz duality isomorphism to the canonical radius derivative. `radiusGradient_eq_extension` connects it to the actual gradient of a valid extension, rather than to an independently assumed vector field.

`derivativeEquiv` comes from the nonsingular local extension in the original diffeomorphism assumptions; `derivativeEquiv_eq_ambientDerivative` connects it to the derivative already proved independent of the extension. The forward operator in `InverseTranspose` is the adjoint of the inverse operator, and its inverse is the adjoint of the original operator. These are `Df^{-T}` and `Df^T` in the real Euclidean setting.

### R3 — Continuity of the Linear Lift and Its Inverse: ACCEPT

`VaryingLinearLift.continuous_linearEquiv_symm` derives continuity of the inverse operators from operator-norm continuity of the forward operators; the former is not introduced as an additional assumption. The normalization denominator is nonzero because the operator is invertible and the input has unit norm.

The target of `LinearLiftHomeomorph.mapImageHomeomorph` is the actual `f(X)` subtype. Continuity of its inverse follows from local extensions of the original inverse function. The inverse position in `linearLiftHomeomorph` is the given `f^{-1}`, and the inverse normal is obtained by the corresponding transpose action followed by normalization. Closedness of `f(X)` does not enter the argument.

### R4 — Differentiation Along Rays and Strict Monotonicity on a Nonconvex Domain: ACCEPT

`RayMonotonicity.hasDerivAt_radius_ray` applies only when the ray genuinely stays in `X` over a parameter neighborhood. It chooses a local extension in the ambient space, differentiates along the ray, and transfers the derivative back to the actual radius using local equality along that ray.

`strictMonoOn_radius_ray` uses relative continuity of the actual radius on a closed interval and requires a derivative only at interior points of that interval. The derivative is

`1 + inner (radiusGradientOnAmbient (z - t • u)) u`.

The unit norm of `u` and the pointwise gradient bound make this derivative strictly positive. Thus `X` need not be convex, the entire infinite ray need not remain in `X`, and no uniform contraction constant is required.

### R5 — The Closed Set of Admissible Centers and the Exponential Lift Embedding: ACCEPT

`ExponentialEmbedding.admissibleCentres` requires the center to belong to `X` and every point `y + ε(y) • v` with `‖v‖≤1` to belong to `X`. The fixed unit-ball formulation allows this condition to be written as an arbitrary intersection of closed sets; continuity is used only on the closed-domain subtype.

`admissibleCentres_ball_subset` connects this condition to the actual constituent ball through the closed-ball affinity identity for a nonnegative radius. That identity includes radius 0, so zero radius is not lost here.

On the closed subset of admissible centers, if the exponential lift's output position belongs to a bounded set, the input center's norm can increase by at most the original `radius_bound`; the input normal always has unit norm. The preimage of a compact output set is therefore contained in a compact subset of the input bundle and is closed by continuity, hence compact. Properness together with the proved injectivity gives a closed embedding.

This argument uses finite dimensionality, the original radius upper bound, and closedness of the center set. The final treatment of `f(X)` is a **subspace restriction** of the embedding on the larger admissible set, so `f(X)` itself may be nonclosed. The inverse-continuity conclusion of the paper is preserved.

### R6 — Existence and Surjectivity in the Full-Image Case: ACCEPT

`SelfSurjectivity` derives from `f(X)=X` that the constituent ball of every domain center lies in `X`. A boundary center with positive radius would be an interior point, a contradiction; therefore the radius is 0 on `frontier X`.

Extending the radius by 0 outside the domain produces only a **continuous** function; the file does not claim that this extension is smooth. The continuous function `q ↦ radiusZeroExtension (z - q • u)` maps `[0,R]` into itself, and a one-dimensional interval fixed-point/intermediate-value argument gives `q = radiusZeroExtension (z-q•u)`.

If the resulting center were outside `X`, the zero extension would force `q=0`, making the center equal to `z`, which already belongs to `X`. This is a contradiction. Thus the root really lies in the original domain. The inverse normal formula and surjectivity of the linear lift then yield surjectivity of the actual beta map.

This is a valid replacement for the original first-exit argument. It does not require a convex, connected, or compact domain, or an everywhere-positive radius; the root-existence step does not even require contraction.

### R7 — Necessity of Contraction: ACCEPT

In dimension at least 2, `ContractionNecessity` constructs a unit vector orthogonal to a nonzero gradient. If the gradient norm is at least 1, the radicands for both `n` and `-n` are nonpositive.

Lean's `Real.sqrt` is a total function and equals 0 on nonpositive inputs. The normal outputs for these two inputs are therefore both the negative gradient, and their position outputs are also equal. A unit vector cannot equal its negative, so injectivity of the raw normal/exponential formula already forces the gradient norm to be strictly less than 1. The proof covers both gradient norm equal to 1 and gradient norm greater than 1, without slipping validity of the radicand or contraction into the hypotheses.

### R8 — The Candidate Formula and Equivalence in Theorem 3.17: ACCEPT

`ContractionCharacterization.boundaryFormula` takes only a system as a parameter, not contraction. The `linearLift` it uses also does not require contraction. The initial target is ambient `E × E`, so construction of a unit-normal subtype does not presuppose the conclusion to be proved.

`BoundaryFormulaIsBijection` is `Set.BijOn` from the entire input bundle to `domain ×ˢ {n | ‖n‖ = 1}`, and includes:

1. Every output position belongs to the domain, and every output normal has norm 1.
2. Injectivity.
3. Surjectivity onto the complete target bundle.

The forward direction combines well-definedness and injectivity of the actual beta map with full-image surjectivity. In the reverse direction, surjectivity of the linear lift when `f(X)=X` transfers injectivity of the candidate beta map to the exponential formula on the entire domain, after which R7 applies. No contraction witness is extracted from the conclusion to define the candidate formula, so there is no circularity.

The totalized square root differs superficially from the paper's real square-root expression, but it causes no false acceptance in this equivalence: R7 excludes every case with gradient norm at least 1; after contraction is established, the original radicand is strictly positive and the output has unit norm. Thus the predicate has the same truth value as the paper's condition that the formula be well-defined and give a bijection.

## Completed Scope and Conclusions Not Yet Covered

- The topological content of Theorem 3.14: the actual beta map is a homeomorphism onto its actual range, with continuous inverse; when `f(X)=X`, it is a homeomorphism of the entire domain bundle.
- Theorem 3.17: equivalence between the candidate formula giving a bijection of the complete bundle and pointwise contraction.
- The zero-radius conclusion of Proposition 3.15 has been implemented, but it is among this agent's contributions, so this report does not count its own reading as independent review.
- The results at this stage do not claim to formalize the contributor–recipient geometry, all boundary-correspondence lemmas, higher local regularity of class `C^(min(r,s)-1)`, or the main results of Section 4.

Final acceptance of “no `sorry` and no new unproved axioms” should rest on compilation of the latest complete project source and an axiom audit that expands dependencies. This report judges only the mathematical meaning, assumptions, and noncircularity of the source read above; it does not equate successful compilation with fidelity to the paper.

## Additional Independent Review by the Lead Agent

The lead agent also read in full and reviewed the new modules from other authors in this round: ExponentialInjectivity, BoundaryInjectivity, LinearLiftHomeomorph, SelfSurjectivity, BoundaryHomeomorph, and ContractionNecessity. Every decision was ACCEPT.

- In ExponentialInjectivity, the two roots correspond to the same output position and unit direction. The radius comparison uses only containment of the ball centered at the point with the larger radius, thereby placing the entire intervening ray segment in X. Exchanging the centers yields equality of radii, after which the center and input normal are recovered. The general admissible-center interface does not assume injectivity.
- BoundaryInjectivity transfers equality of actual beta outputs to the actual E map, uses that the true image of L lies in f(X), and finally uses injectivity of L. The coordinates of all three maps agree.
- The explicit inverse in LinearLiftHomeomorph first recovers the deterministic source point and then computes the transpose action at that same source point. Continuity of the inverse operators comes from the proved continuous-operator-field result, and continuity of source-point recovery comes from the existing inverse_extension.
- SelfSurjectivity extends ball containment to all domain centers only under the full-image condition. Zero radius on the boundary ensures continuous gluing. If the center obtained from the interval fixed point were outside the domain, the ray parameter would have to be zero, contradicting that the output lies in the domain. Recovering the normal and the preimage under L then gives surjectivity of the actual beta map.
- BoundaryHomeomorph restricts the E embedding on the closed admissible-center set to the actual f(X), then composes it with the L homeomorphism. Continuous inclusion of the output subtype recovers the beta embedding, which is then packaged as a Homeomorph onto the actual range. The full-image case separately uses actual surjectivity. A continuous bijection is not simply treated as a homeomorphism.
- ContractionNecessity uses dimension at least two to obtain an orthogonal direction and unit length to exclude n = -n. When the gradient norm is at least one, both position and normal outputs collide. The conclusion concerns the canonical radiusGradient, not another representative.

RayMonotonicity, ExponentialEmbedding, and ContractionCharacterization, written by the lead agent in this round, were independently reviewed by the other agent above; the lead agent's self-check is not substituted for independent review. The first batch's independent review is preserved in semantic-review-first-batch.md. See verification.json and verification.txt for the final source hashes, compilation records, and axiom-audit records.
