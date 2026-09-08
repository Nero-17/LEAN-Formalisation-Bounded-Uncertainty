import BoundedUncertainty.Section3Interfaces
import BoundedUncertainty.ContractionNecessity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.FinCases

/-! A genuine system showing why Definition 3.9 needs its stated well-definedness qualification:
the unconditional raw formula can fail to take values in the unit sphere. -/
namespace BoundedUncertainty
open Set

noncomputable def oscillatingRadius (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  2 + Real.sin (2 * p 0)

theorem contDiff_oscillatingRadius (order : WithTop ℕ∞) : ContDiff ℝ order oscillatingRadius := by
  unfold oscillatingRadius
  fun_prop

noncomputable def unconditionedExponentialSystem :
    SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) 1 1 where
  dimension_at_least_two := by simp
  domain := univ
  regular_closed := by simp [IsRegularClosed]
  map := id
  radius := oscillatingRadius
  radius_bound := 3
  radius_bound_pos := by norm_num
  radius_order_pos := le_rfl
  map_order_pos := le_rfl
  map_into_domain := mapsTo_id _
  diffeomorphism := ambientDiffeomorphismOn_id 1 univ
  radius_extension := hasLocalExtensionOn_of_contDiff 1 univ _ (contDiff_oscillatingRadius 1)
  radius_nonneg := fun p _ => by dsimp [oscillatingRadius]; linarith [Real.neg_one_le_sin (2 * p 0)]
  radius_le_bound := fun p _ => by dsimp [oscillatingRadius]; linarith [Real.sin_le_one (2 * p 0)]
  ball_into_domain := fun _ _ => subset_univ _

theorem hasGradientAt_oscillatingRadius_zero :
    HasGradientAt oscillatingRadius (!₂[2, 0] : EuclideanSpace ℝ (Fin 2)) 0 := by
  have hcoordinate := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt
    (x := (0 : EuclideanSpace ℝ (Fin 2)))
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasFDerivAt_const (2 : ℝ) (0 : EuclideanSpace ℝ (Fin 2))).add
    (((hasFDerivAt_const (2 : ℝ) (0 : EuclideanSpace ℝ (Fin 2))).mul hcoordinate).sin) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem unconditionedExponentialSystem_gradient_zero :
    unconditionedExponentialSystem.radiusGradient ⟨0, mem_univ _⟩ = !₂[2, 0] := by
  let extension : LocalExtensionAt 1 univ oscillatingRadius (0 : EuclideanSpace ℝ (Fin 2)) := {
    neighborhood := univ
    isOpen_neighborhood := isOpen_univ
    mem_neighborhood := mem_univ _
    extension := oscillatingRadius
    contDiffOn_extension := (contDiff_oscillatingRadius 1).contDiffOn
    agrees := fun _ _ => rfl
  }
  rw [unconditionedExponentialSystem.radiusGradient_eq_extension
    (by decide : 1 ≤ 1) extension ⟨0, mem_univ _⟩ (mem_univ _)]
  exact hasGradientAt_oscillatingRadius_zero.gradient

/-- The failure occurs in a fully admissible two-dimensional system, not merely in free vector algebra. -/
theorem exists_system_raw_exponential_not_unit :
    ∃ system : SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) 1 1,
      ∃ y : system.domain, ∃ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 ∧
        ‖(exponentialMap system.radius system.radiusGradientOnAmbient
          ((y : EuclideanSpace ℝ (Fin 2)), n)).2‖ ≠ 1 := by
  refine ⟨unconditionedExponentialSystem, ⟨0, mem_univ _⟩, !₂[0, 1], ?_, ?_⟩
  · norm_num [EuclideanSpace.norm_eq]
  · change ‖normalUpdate (unconditionedExponentialSystem.radiusGradientOnAmbient 0) !₂[0, 1]‖ ≠ 1
    rw [unconditionedExponentialSystem.radiusGradientOnAmbient_apply ⟨0, mem_univ _⟩,
      unconditionedExponentialSystem_gradient_zero,
      normalUpdate_of_orthogonal_of_one_le_norm (!₂[2, 0] : EuclideanSpace ℝ (Fin 2)) !₂[0, 1]]
    · norm_num [EuclideanSpace.norm_eq]
    · norm_num [EuclideanSpace.norm_eq]
    · norm_num [PiLp.inner_apply, Fin.sum_univ_two]

end BoundedUncertainty
