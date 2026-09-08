import BoundedUncertainty.CanonicalDerivative
import BoundedUncertainty.ExponentialMap
import BoundedUncertainty.InverseTranspose

/-!
The actual radius gradient, differential and boundary-map formula.
All derivative data are obtained from local extensions already present in
Definition 3.1. Contraction is pointwise. The domain and radius may have boundary
and zeros, respectively. This module does not assert global bijectivity of beta.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

noncomputable def SetValuedSystem.radiusGradient
    (system : SetValuedSystem (E := E) r s) (y : system.domain) : E :=
  (InnerProductSpace.toDual ℝ E).symm (system.radius_extension.ambientDerivative y)

theorem SetValuedSystem.radiusGradient_eq_extension
    (system : SetValuedSystem (E := E) r s) {order : ℕ} (horder : 1 ≤ order)
    {x : E} (extension : LocalExtensionAt order system.domain system.radius x)
    (y : system.domain) (hy : (y : E) ∈ extension.neighborhood) :
    system.radiusGradient y = gradient extension.extension y := by
  exact congrArg (InnerProductSpace.toDual ℝ E).symm
    (system.radius_extension.ambientDerivative_eq_extension system.regular_closed
      system.radius_order_pos horder extension y hy)

theorem SetValuedSystem.continuous_radiusGradient
    (system : SetValuedSystem (E := E) r s) :
    Continuous system.radiusGradient :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (system.radius_extension.continuous_ambientDerivative
      system.regular_closed system.radius_order_pos)

/-- Extension by zero is only a total-function representation; no smoothness
outside the domain is asserted or used. -/
noncomputable def SetValuedSystem.radiusGradientOnAmbient
    (system : SetValuedSystem (E := E) r s) (y : E) : E := by
  classical
  exact if hy : y ∈ system.domain then system.radiusGradient ⟨y, hy⟩ else 0

@[simp] theorem SetValuedSystem.radiusGradientOnAmbient_apply
    (system : SetValuedSystem (E := E) r s) (y : system.domain) :
    system.radiusGradientOnAmbient y = system.radiusGradient y := by
  simp [SetValuedSystem.radiusGradientOnAmbient, y.property]

theorem SetValuedSystem.continuousOn_radiusGradientOnAmbient
    (system : SetValuedSystem (E := E) r s) :
    ContinuousOn system.radiusGradientOnAmbient system.domain := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : system.domain.restrict system.radiusGradientOnAmbient =
      system.radiusGradient := by
    funext y
    exact system.radiusGradientOnAmbient_apply y
  rw [heq]
  exact system.continuous_radiusGradient

def SetValuedSystem.IsContraction (system : SetValuedSystem (E := E) r s) : Prop :=
  ∀ y : system.domain, ‖system.radiusGradient y‖ < 1

theorem SetValuedSystem.IsContraction.norm_radiusGradientOnAmbient
    {system : SetValuedSystem (E := E) r s} (h : system.IsContraction)
    (y : E) (hy : y ∈ system.domain) : ‖system.radiusGradientOnAmbient y‖ < 1 := by
  simpa only [SetValuedSystem.radiusGradientOnAmbient, dif_pos hy] using h ⟨y, hy⟩

/-- The nonsingular derivative selected from the given local extension. -/
noncomputable def SetValuedSystem.derivativeEquiv
    (system : SetValuedSystem (E := E) r s) (x : system.domain) : E ≃L[ℝ] E :=
  (Classical.choice (system.diffeomorphism.nonsingular x x.property)).derivative

omit [CompleteSpace E] in
/-- The selected equivalence really is the extension-independent differential. -/
theorem SetValuedSystem.derivativeEquiv_eq_ambientDerivative
    (system : SetValuedSystem (E := E) r s) (x : system.domain) :
    (system.derivativeEquiv x : E →L[ℝ] E) =
      system.diffeomorphism.forward_extension.ambientDerivative x := by
  rw [system.diffeomorphism.forward_extension.ambientDerivative_eq_extension
    system.regular_closed system.map_order_pos system.map_order_pos
    (Classical.choice (system.diffeomorphism.nonsingular x x.property)).toLocalExtensionAt
    x (Classical.choice (system.diffeomorphism.nonsingular x x.property)).mem_neighborhood]
  exact (Classical.choice
    (system.diffeomorphism.nonsingular x x.property)).hasFDerivAt_extension.fderiv.symm

/-- Definition 3.9 and Proposition 3.10 with the genuine radius gradient. -/
noncomputable def SetValuedSystem.exponentialLift
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    system.domain × {n : E // ‖n‖ = 1} → E × {n : E // ‖n‖ = 1} :=
  exponentialBundleMap system.domain system.radius system.radiusGradientOnAmbient
    hcontraction.norm_radiusGradientOnAmbient

theorem SetValuedSystem.continuous_exponentialLift
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    Continuous (system.exponentialLift hcontraction) :=
  continuous_exponentialBundleMap system.domain system.radius system.radiusGradientOnAmbient
    hcontraction.norm_radiusGradientOnAmbient
    system.radius_extension.continuousOn system.continuousOn_radiusGradientOnAmbient

/-- The cotangent lift from Definition 3.11, with its image embedded in X.
Its first coordinate belongs to f(X); the next theorem records that fact. -/
noncomputable def SetValuedSystem.linearLift
    (system : SetValuedSystem (E := E) r s) :
    system.domain × {n : E // ‖n‖ = 1} → system.domain × {n : E // ‖n‖ = 1} :=
  fun p => (⟨system.map p.1, system.map_into_domain p.1.property⟩,
    normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv p.1)) p.2)

theorem SetValuedSystem.linearLift_position_mem_image
    (system : SetValuedSystem (E := E) r s)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    ((system.linearLift p).1 : E) ∈ system.map '' system.domain :=
  ⟨p.1, p.1.property, rfl⟩

theorem SetValuedSystem.exponential_linearLift_position_mem
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    (system.exponentialLift hcontraction (system.linearLift p)).1 ∈ system.domain := by
  apply system.ball_into_domain p.1 p.1.property
  exact exponentialMap_position_mem_closedBall system.radius system.radiusGradientOnAmbient
    (system.map p.1)
    (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv p.1)) p.2)
    (system.radius_nonneg _ (system.map_into_domain p.1.property))
    (hcontraction.norm_radiusGradientOnAmbient _ (system.map_into_domain p.1.property))
    (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv p.1)) p.2).property

/-- Definition 3.11: beta is E composed with L, and F(X) subset X proves its codomain. -/
noncomputable def SetValuedSystem.boundaryMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    system.domain × {n : E // ‖n‖ = 1} → system.domain × {n : E // ‖n‖ = 1} :=
  fun p => (⟨(system.exponentialLift hcontraction (system.linearLift p)).1,
    system.exponential_linearLift_position_mem hcontraction p⟩,
    (system.exponentialLift hcontraction (system.linearLift p)).2)

end BoundedUncertainty
