# Section 3 Lean formalization: independent semantic review

Date: 2026-09-08. Reviewer: `/root/lean_lift`.

**Disposition: ACCEPT for the explicitly documented completed scope.** No semantic mismatch or hidden strengthening was found in the four reviewed integration modules. This does not certify the unproved global parts of Theorem 3.14.

## Scope and independence

I read `BoundaryMap.lean`, `BoundaryContinuity.lean`, `CanonicalDerivative.lean`, `ZeroRadius.lean`, and the README in `outputs/bounded-uncertainty-lean`. These four modules were written by the root or another agent, not by this reviewer. I also read the local-extension and nonsingular-extension definitions in `Basic.lean`, the interface to `exponentialMap` in `ExponentialMap.lean`, and the manuscript's gradient/contraction notation and Proposition 3.15 at the fixed online source snapshot `3200c88`.

This review does **not** count my own `AmbientDerivative.lean`, `LinearLift.lean`, `InverseTranspose.lean`, or `VaryingLinearLift.lean` as independently reviewed evidence. Their interface contracts are inputs to the integration review. The root reports an 11-module rebuild with exit code 0 and a 94-declaration axiom audit containing only `propext`, `Classical.choice`, and `Quot.sound`; I did not rerun compilation or claim an independent compiler audit in this bounded review.

## Material checks

1. **Canonical derivative selection — ACCEPT.** `HasLocalExtensionOn.ambientDerivative` takes the actual `fderiv` of a selected smooth local extension. It is not the derivative of an arbitrary ambient representative outside the domain. `ambientDerivative_eq_extension` uses equality of extensions on their common intersection with the regular closed domain and their positive differentiability orders to identify derivatives. Its proof compares two genuine local extensions. `continuous_ambientDerivative` then identifies the selected field locally with one fixed extension's continuous derivative; it does not assume that a choice function varies continuously.

2. **Gradient identification — ACCEPT.** `radiusGradient` is the inverse Riesz map applied to this canonical radius differential. `radiusGradient_eq_extension` identifies it with the genuine gradient of each admissible radius extension at relevant domain points. `radiusGradientOnAmbient` is merely a total representation: only its restriction to the domain is used for continuity and contraction. No smoothness of the zero extension outside the domain is asserted.

3. **Actual differential and inverse-transpose wiring — ACCEPT.** `derivativeEquiv` is selected from a `NonsingularLocalExtensionAt`, whose data include an actual `HasFDerivAt` assertion for the same extension. `derivativeEquiv_eq_ambientDerivative` establishes equality of its forward operator with the canonical differential. The linear lift then evaluates `inverseTranspose (system.derivativeEquiv p.1)` at the source point, applies the normalized sphere homeomorphism to the incoming normal, and uses `system.map p.1` as its position. Thus it uses the source differential with the inverse-transpose API; the radius and its gradient are subsequently evaluated at the deterministic image by the exponential lift. It is not an unrelated assumed vector or derivative field.

4. **Domain and radius hypotheses — ACCEPT.** `IsContraction` is exactly `∀ y : system.domain, ‖system.radiusGradient y‖ < 1`. There is no uniform constant below one. No convexity or positive lower bound on the radius enters these four modules. The boundary map's first coordinate belongs to the original domain by `ball_into_domain` at the source and the actual radius at its deterministic image. This does not require every radius ball centered at an arbitrary point of the domain to remain inside the domain, or require `f(X)=X`.

5. **Continuity versus invertibility — ACCEPT.** `continuous_derivativeEquiv` derives continuity from canonical-derivative equality; `continuous_linearLift` uses the joint inverse-transpose normalization API; and `continuous_boundaryMap` is continuity of the actual composition with the necessary subtype codomain proof. `linearLift_injective` and `range_linearLift` concern the linear lift only. None of the four files claims global injectivity, inverse continuity, or a homeomorphism for the full exponential map or beta. The README explicitly lists those parts of Theorem 3.14 as unfinished and labels the proven beta result as its continuous part.

6. **Zero-radius restrictions — ACCEPT.** Generic gradient-zero lemmas require an ambient local minimum or ambient eventual nonnegativity. The system-level theorem obtains this from `y ∈ interior system.domain`; nonnegativity is transferred to the local extension only on an actual neighborhood contained in the domain. The whole-space version is then a valid specialization. The resulting fixed-pair statements concern the exponential map/lift, not beta. A zero radius at an arbitrary boundary point is never used to infer a zero ambient gradient or fixed normal. This agrees with Proposition 3.15 and its following remark in the fixed manuscript.

7. **README completion claims — ACCEPT.** The README distinguishes the implemented finite differentiability orders from an unimplemented separate smooth-infinite-order interface. It lists Lemmas 3.4–3.8, the global/inverse/higher-regularity parts of Theorem 3.14, and Theorem 3.17 as unfinished. The statements concerning the actual gradient, local extension independence, genuine inverse-transpose lift, beta continuity, and whole-space/interior zero-radius result match the inspected modules. No entire-section completion claim is made.

## Audited snapshot

SHA-256 values read after inspection:

| File | SHA-256 |
|---|---|
| `BoundaryMap.lean` | `0B56602CFEF17FF494A40EC73474C1B558FECF0F9E757302B799E7E8882259BC` |
| `BoundaryContinuity.lean` | `5C13F257DE763A6BED9F8DD795FF412E15DB7FA4E6D76FC21C6BF787AA290F8A` |
| `CanonicalDerivative.lean` | `395B47C411B4F0D365D00B6B6959257F089A67133F60B1230F30B83881A60B31` |
| `ZeroRadius.lean` | `28AF1BD995E5B4651C99203D571A12D4C4ECF070F73E7FF91B9DC6AB3D89BE01` |
| `README.md` | `DEA89549847541F6E55023FFAC7CB87B3AB3F1FB4FCD81EA696D9E590B930066` |

No code or documentation was modified by this review.
