import BoundedUncertainty.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Module

/-! Coordinates adapted to a nonzero normal covector. The horizontal space
is its actual kernel, with the inherited norm and topology. -/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Split off a transverse direction on which the covector has value one. -/
noncomputable def normalCoordinates (normal : E →L[ℝ] ℝ) (vertical : E)
    (hnormal : normal vertical = 1) : E ≃L[ℝ] ℝ × normal.ker :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun point => (normal point,
        ⟨point - normal point • vertical, by
          change normal (point - normal point • vertical) = 0
          simp [hnormal]⟩)
      invFun := fun point => point.1 • vertical + point.2
      left_inv := by intro point; simp
      right_inv := by
        rintro ⟨height, horizontal⟩
        have hhorizontal : normal horizontal = 0 := horizontal.property
        apply Prod.ext
        · simp [hnormal, hhorizontal]
        · apply Subtype.ext
          simp only [map_add, map_smul, hnormal, hhorizontal, smul_eq_mul, mul_one, add_zero]
          module
      map_add' := by
        intro point other
        apply Prod.ext
        · exact map_add normal point other
        · apply Subtype.ext
          change (point + other) - normal (point + other) • vertical =
            (point - normal point • vertical) + (other - normal other • vertical)
          simp only [map_add, add_smul]
          module
      map_smul' := by
        intro scalar point
        apply Prod.ext
        · exact map_smul normal scalar point
        · apply Subtype.ext
          change scalar • point - normal (scalar • point) • vertical =
            scalar • (point - normal point • vertical)
          simp only [map_smul, smul_eq_mul]
          module }

theorem normalCoordinates_fst (normal : E →L[ℝ] ℝ) (vertical : E)
    (hnormal : normal vertical = 1) (point : E) :
    (normalCoordinates normal vertical hnormal point).1 = normal point := rfl

theorem normalCoordinates_symm_apply (normal : E →L[ℝ] ℝ) (vertical : E)
    (hnormal : normal vertical = 1) (point : ℝ × normal.ker) :
    (normalCoordinates normal vertical hnormal).symm point = point.1 • vertical + point.2 := rfl

end BoundedUncertainty
