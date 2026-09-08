import BoundedUncertainty.ZeroRadius
import BoundedUncertainty.HigherBoundaryMap

/-! Remark 3.12: a radius constant only on the original domain gives the
classical boundary formula. No constancy of its ambient representative is needed. -/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

theorem SetValuedSystem.radiusGradient_eq_zero_of_constant
    (system : SetValuedSystem (E := E) r s) (radius : ℝ)
    (hconstant : ∀ y ∈ system.domain, system.radius y = radius)
    (y : system.domain) : system.radiusGradient y = 0 := by
  let extension : LocalExtensionAt r system.domain system.radius y := {
    neighborhood := univ
    isOpen_neighborhood := isOpen_univ
    mem_neighborhood := mem_univ _
    extension := fun _ => radius
    contDiffOn_extension := contDiffOn_const
    agrees := fun z hz => (hconstant z hz.1).symm
  }
  rw [system.radiusGradient_eq_extension system.radius_order_pos extension y (mem_univ _)]
  exact (hasGradientAt_const (y : E) radius).gradient

theorem SetValuedSystem.isContraction_of_constant_radius
    (system : SetValuedSystem (E := E) r s) (radius : ℝ)
    (hconstant : ∀ y ∈ system.domain, system.radius y = radius) :
    system.IsContraction := by
  intro y
  rw [system.radiusGradient_eq_zero_of_constant radius hconstant y, norm_zero]
  exact zero_lt_one

/-- The full classical formula with the actual inverse-transpose normal. -/
theorem SetValuedSystem.boundaryFormula_of_constant_radius
    (system : SetValuedSystem (E := E) r s) (radius : ℝ)
    (hconstant : ∀ y ∈ system.domain, system.radius y = radius)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    system.boundaryFormula p =
      (system.map p.1 + radius • normalizedLinearMap (inverseTranspose (system.derivativeEquiv p.1)) p.2,
        normalizedLinearMap (inverseTranspose (system.derivativeEquiv p.1)) p.2) := by
  have hgradient : system.radiusGradientOnAmbient (system.map p.1) = 0 := by
    rw [system.radiusGradientOnAmbient_apply
      ⟨system.map p.1, system.map_into_domain p.1.property⟩]
    exact system.radiusGradient_eq_zero_of_constant radius hconstant _
  simp only [SetValuedSystem.boundaryFormula, SetValuedSystem.linearLift,
    exponentialMap, hgradient, normalUpdate_zero_gradient,
    hconstant _ (system.map_into_domain p.1.property)]
  rfl

end BoundedUncertainty
