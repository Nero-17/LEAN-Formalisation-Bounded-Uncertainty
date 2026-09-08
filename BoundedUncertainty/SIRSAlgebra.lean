import BoundedUncertainty.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-! Exact algebra and smooth polynomial data for Example 3.13. All state
vectors live in EuclideanSpace, with the Euclidean norm rather than a product max norm. -/

namespace BoundedUncertainty

open Set

def sirsSimplex : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1}

noncomputable def sirsMap (h a b : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  !₂[p 0 + h * (-b * p 0 * p 1 + (1 - p 0 - p 1) / 2),
    p 1 + h * (b * p 0 * p 1 - a * p 1)]

noncomputable def sirsRadius (κ : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (κ / 10) * p 0 * p 1 * (1 - p 0 - p 1)

noncomputable def sirsRadiusGradient (κ : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  !₂[(κ / 10) * p 1 * (1 - 2 * p 0 - p 1),
    (κ / 10) * p 0 * (1 - p 0 - 2 * p 1)]

theorem contDiff_sirsRadius (κ : ℝ) (order : WithTop ℕ∞) :
    ContDiff ℝ order (sirsRadius κ) := by
  unfold sirsRadius
  fun_prop

theorem contDiff_sirsRadiusGradient (κ : ℝ) (order : WithTop ℕ∞) :
    ContDiff ℝ order (sirsRadiusGradient κ) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [sirsRadiusGradient] <;> fun_prop

theorem contDiff_sirsMap (h a b : ℝ) (order : WithTop ℕ∞) :
    ContDiff ℝ order (sirsMap h a b) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [sirsMap] <;> fun_prop

theorem sirsMap_first_coordinate (p : EuclideanSpace ℝ (Fin 2)) :
    sirsMap (1 / 10) 1 3 p 0 = p 0 * (1 - (3 / 10) * p 1) + (1 / 20) * (1 - p 0 - p 1) := by
  dsimp [sirsMap]
  ring

theorem sirsMap_second_coordinate (p : EuclideanSpace ℝ (Fin 2)) :
    sirsMap (1 / 10) 1 3 p 1 = p 1 * (9 / 10 + (3 / 10) * p 0) := by
  dsimp [sirsMap]
  ring

theorem sirsMap_recovered_coordinate (p : EuclideanSpace ℝ (Fin 2)) :
    1 - sirsMap (1 / 10) 1 3 p 0 - sirsMap (1 / 10) 1 3 p 1 =
      (19 / 20) * (1 - p 0 - p 1) + (1 / 10) * p 1 := by
  rw [sirsMap_first_coordinate, sirsMap_second_coordinate]
  ring

theorem sirsMap_mapsTo : MapsTo (sirsMap (1 / 10) 1 3) sirsSimplex sirsSimplex := by
  intro p hp
  rcases hp with ⟨hS, hI, hsum⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [sirsMap_first_coordinate]
    exact add_nonneg (mul_nonneg hS (by linarith)) (mul_nonneg (by norm_num) (by linarith))
  · rw [sirsMap_second_coordinate]
    exact mul_nonneg hI (by linarith)
  · have hnonneg : 0 ≤ 1 - sirsMap (1 / 10) 1 3 p 0 - sirsMap (1 / 10) 1 3 p 1 := by
      rw [sirsMap_recovered_coordinate]
      exact add_nonneg (mul_nonneg (by norm_num) (by linarith))
        (mul_nonneg (by norm_num) hI)
    linarith

theorem sirsRadius_nonneg (κ : ℝ) (hκ : 0 ≤ κ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) : 0 ≤ sirsRadius κ p := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hκ (by norm_num)) hp.1) hp.2.1)
    (by linarith [hp.2.2])

/-- The unscaled squared Euclidean gradient has maximum 1/8 on the simplex. -/
theorem sirs_gradient_polynomial_bound (S I : ℝ) (hS : 0 ≤ S) (hI : 0 ≤ I)
    (hsum : S + I ≤ 1) :
    (I * (1 - 2 * S - I)) ^ 2 + (S * (1 - S - 2 * I)) ^ 2 ≤ 1 / 8 := by
  have hproduct : 0 ≤ S * I := mul_nonneg hS hI
  have hproductUpper : S * I ≤ (S + I) ^ 2 / 4 := by nlinarith [sq_nonneg (S - I)]
  have hconvex := mul_nonneg hproduct (sub_nonneg.mpr hproductUpper)
  have hparabola : 0 ≤ (S + I) * (1 - (S + I)) :=
    mul_nonneg (add_nonneg hS hI) (sub_nonneg.mpr hsum)
  have hparabolaUpper : (S + I) * (1 - (S + I)) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (2 * (S + I) - 1)]
  have hendpointZero : (S + I) ^ 2 * (1 - (S + I)) ^ 2 ≤ 1 / 16 := by
    nlinarith [sq_nonneg ((S + I) * (1 - (S + I)) - 1 / 4)]
  have hquadraticLower : -1 ≤ (S + I) * (3 * (S + I) - 2) := by
    nlinarith [sq_nonneg (3 * (S + I) - 1)]
  have hquadraticUpper : (S + I) * (3 * (S + I) - 2) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsum) (by linarith : 0 ≤ 3 * (S + I) + 1)]
  have hendpointQuarter : (S + I) ^ 2 * (3 * (S + I) - 2) ^ 2 / 8 ≤ 1 / 8 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (S + I) * (3 * (S + I) - 2))
      (by linarith : 0 ≤ 1 + (S + I) * (3 * (S + I) - 2))]
  by_cases hcoefficient : 0 ≤ (S + I) ^ 2 / 2 - 2 * (1 - (S + I))
  · have hendpoint := mul_nonneg (sub_nonneg.mpr hproductUpper) hcoefficient
    nlinarith
  · have hendpoint := mul_nonpos_of_nonneg_of_nonpos hproduct (le_of_not_ge hcoefficient)
    nlinarith

end BoundedUncertainty
