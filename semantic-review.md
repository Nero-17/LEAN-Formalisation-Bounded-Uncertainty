**Historical review:** This document records the review at the 38-module stage. Current coverage is documented in [section3-coverage-review.md](section3-coverage-review.md).

**Section 3: Independent Semantic Review of Boundary Geometry and Higher Regularity**

Date: 2026-09-08. Manuscript baseline: 3200c88826c73210d1e83bfc46de1656ee0788ef.

This report records the mathematical meaning and assumptions of the source code. Compilation and axiom verification are documented separately in verification.txt/json. Earlier rounds are recorded in semantic-review-topology.md and semantic-review-first-batch.md.

| Independent reviewer | Other agents' source code reviewed in this round | Verdict |
|---|---|---|
| lean_normal_algebra | BoundaryContributors, LocalBoundary, ContactGeometry | ACCEPT, with a scope qualification concerning the bridge to local boundary models |
| lean_lift | ContributorFormula, BoundaryInverseRepresentation, HigherBoundaryInverse | ACCEPT, with scope qualifications concerning finite orders and tangent-space interfaces |
| Lead agent | InflationGeometry, BoundaryNormalAlgebra, SphereBoundary, C1BoundaryGraph, ContributorFormula, and all 8 agent-authored modules concerning higher regularity, implicit functions, and local-extension operations | ACCEPT |

The lead agent authored BoundaryContributors, LocalBoundary, ContactGeometry, BoundaryInverseRepresentation, and HigherBoundaryInverse; another agent performed their independent review. No agent counted a review of their own modules as an independent review.

**Contributing Centers and Inflation**

InflationGeometry proves compactness by expressing the inflation as the continuous image of the product of B and the closed unit ball under (y,u)↦y+radius(y)u. Only relative continuity of the radius on B is required, and the parameterization remains valid at zero radius. Positive-radius balls are covered by the closure of their interior points; zero-radius centers are handled using the regular closedness of B and the inclusion of B in its inflation.

The pointwise lemmas in BoundaryContributors do not require compactness of the center set or smoothness of its boundary. An interior contributor with positive radius makes q−radius(z−qu) attain a local minimum at its root, whereas the derivative of the actual local extension is 1+inner(gradient,u)>0, a contradiction. At zero radius, z=y first rules out an interior contributor. The final inclusion uses compactness to prove that a contributor exists, rather than hiding existence in a hypothesis.

**C1 Boundaries, Signed Multipliers, and the Actual Formula**

C1BoundaryAt supplies only a local nonpositive defining function for the set and its normalized actual gradient. LocalBoundary uses the sign of a one-sided ray derivative to prove entry into or exit from the set, then derives tangent-cone membership and the derivative inequality at a local maximum. BoundaryNormalAlgebra rigorously converts the half-space inequality into a nonnegative multiple of the normal. Alignment of the normals, frontier membership, and uniqueness of the normal are conclusions, not structure fields.

SphereBoundary computes the actual gradient of squared distance, proves it is nonzero on a positive-radius sphere, and obtains the radial outward normal. ContactGeometry uses ball containment and alignment of the normals to identify the receiving normal; it proves the multiplier's sign using the local maximum on B of the negative squared contact potential. The contact gradient comes from an actual local radius extension and agrees with the canonical gradient. The scaling by −2 and division by 2 are correct.

C1BoundaryGraph allows a one-sided C1 graph chart in arbitrary invertible linear coordinates, without assuming that the graph function has zero derivative at the origin. The transverse derivative is 1, so the gradient is nonzero, yielding boundary data. **A one-sided graph chart has not yet been constructed solely from the assumptions of regular closedness and a C1 hypersurface frontier.** The accepted scope for 3.5–3.8 at this stage is the explicit defining-function / one-sided graph-chart version; successful compilation does not remove this scope limitation.

For positive radius, ContributorFormula uses the actual internally tangent ball and the multiplier relation to show that u+gradient is a nonnegative multiple of the source outward normal. Contraction rules out a zero vector, so the multiple is strictly positive; normalization then allows the established inverse formula for normalUpdate to be applied.

At zero radius, z=y, and set containment makes the two outward normals agree. The radius is nonnegative on B and vanishes at y, so an actual extension of its negative attains a local maximum on B. Hence gradient=(-coefficient)•normal, with coefficient≥0. The normalUpdate identity for a parallel gradient completes the normal formula without assuming that the boundary gradient vanishes. The actual raw E, typed exponentialLift, explicit lambda, and position expression are all connected to manuscript 3.8.

**Higher Regularity and the Implicit-Function Inverse**

HigherDerivative differentiates the original C^r/C^s local extensions pointwise. Uniqueness of the canonical derivative on a regular closed domain identifies the derivative fields on the domain, giving a C^(r−1) gradient and a C^(s−1) differential. It does not require the ambient representative extended by zero outside the domain to be smooth, or assume UniqueDiffOn X.

HigherExponential differentiates the squared norm as an inner product, covering a zero gradient; pointwise contraction makes the radicand strictly positive. HigherLinearLift uses smoothness of operator inversion at the actual invertible differential, and the unit normal ensures that the normalization denominator is nonzero. HigherLinearInverse recovers the source point on the actual f(X), then computes the transpose of the actual differential at that same source point.

Composition in LocalExtensionOperations first shrinks the neighborhood so that the inner extension lands in the outer extension's neighborhood; equalities are used only on valid intersections. Subtracting one in the natural numbers correctly includes C0 when r,s≥1.

ImplicitRadius applies mathlib's higher-order IFT to q−radius(z−qu)=0. The partial derivative comes from an actual HasFDerivAt, and its nonvanishing follows from 1+inner(gradient,u)>0. The conclusion includes the value at the base point, the local equation, and uniqueness in a joint neighborhood.

HigherExponentialInverse takes only an already established continuous right inverse as input. Relative continuity places the recovered center and radius in the extension and uniqueness neighborhoods, so the actual root equals the implicit-function branch. Recovery of the center and normalization of the inverse normal give a C^(r−1) extension. Higher regularity of the inverse is not assumed, and neither positive radius nor a closed image is required.

**The Actual Image of beta and Regularity in Both Directions**

The range used in BoundaryInverseRepresentation is Set.range boundaryFormula, the actual ambient output of the typed candidate formula. On this range, the inverse representative takes the coordinates of the actual homeomorphism inverse; its zero values outside the range carry no regularity claim. The composition identities in both directions agree with the original beta.

In HigherBoundaryInverse, continuity of L∘betaInverse follows from continuity of the actual beta inverse and continuity of L. The right-inverse identity for E is precisely the already proved composition identity for beta. The IFT gives the intermediate inverse regularity C^(r−1), and mapsTo_image ensures that the center belongs to f(X); only then is it composed with the C^(s−1) inverse of L. The final use of L inverse∘L=id is restricted to the actual range, and the order min(r,s)−1 is correct. The full-image branch uses surjectivity only after the explicit assumption f(X)=X. There is no circular assumption.

The completed scope at this stage is a homeomorphism with local coordinate extensions in both directions at finite natural-number orders, reducing to C0 when r=1 or s=1. **A linear equivalence D beta on manifold tangent spaces, a nonsingular bundle-diffeomorphism structure, and a separate C∞ interface have not been constructed.** The finite-order statement of Theorem 3.14 and regularity in both directions have been obtained; these additional interfaces must not also be counted as complete.
