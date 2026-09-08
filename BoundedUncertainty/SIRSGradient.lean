import BoundedUncertainty.SIRSAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity

/-! The true Euclidean gradient, its sharp bound and its attained supremum
in Example 3.13. All constants are exact rational or radical expressions. -/

namespace BoundedUncertainty

open Set

theorem hasGradientAt_sirsRadius (κ : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (sirsRadius κ) (sirsRadiusGradient κ p) p := by
  have hfirst := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := p)
  have hsecond := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := p)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((hasFDerivAt_const (κ / 10) p).mul hfirst).mul hsecond).mul
    (((hasFDerivAt_const (1 : ℝ) p).sub hfirst).sub hsecond) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_two,
    sirsRadiusGradient]
  ring

theorem gradient_sirsRadius (κ : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    gradient (sirsRadius κ) p = sirsRadiusGradient κ p :=
  (hasGradientAt_sirsRadius κ p).gradient

theorem sirsRadiusGradient_norm_sq (κ : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    ‖sirsRadiusGradient κ p‖ ^ 2 = (κ / 10) ^ 2 *
      ((p 1 * (1 - 2 * p 0 - p 1)) ^ 2 + (p 0 * (1 - p 0 - 2 * p 1)) ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  dsimp [sirsRadiusGradient]
  simp only [sq_abs]
  ring

theorem sirsRadiusGradient_norm_sq_le (κ : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    ‖sirsRadiusGradient κ p‖ ^ 2 ≤ κ ^ 2 / 800 := by
  rw [sirsRadiusGradient_norm_sq]
  have hbound := mul_le_mul_of_nonneg_left
    (sirs_gradient_polynomial_bound (p 0) (p 1) hp.1 hp.2.1 hp.2.2) (sq_nonneg (κ / 10))
  convert hbound using 1
  ring

theorem sirsGradientBound_sq (κ : ℝ) :
    (κ / (20 * Real.sqrt 2)) ^ 2 = κ ^ 2 / 800 := by
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sirsRadiusGradient_norm_le (κ : ℝ) (hκ : 0 ≤ κ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    ‖sirsRadiusGradient κ p‖ ≤ κ / (20 * Real.sqrt 2) := by
  have hbound := sirsRadiusGradient_norm_sq_le κ p hp
  have hnonneg : 0 ≤ κ / (20 * Real.sqrt 2) := by positivity
  nlinarith [sirsGradientBound_sq κ, norm_nonneg (sirsRadiusGradient κ p)]

theorem sirsRadiusGradient_norm_attained (κ : ℝ) (hκ : 0 ≤ κ) :
    ‖sirsRadiusGradient κ !₂[(1 : ℝ) / 2, 1 / 2]‖ = κ / (20 * Real.sqrt 2) := by
  have hsq := sirsRadiusGradient_norm_sq κ !₂[(1 : ℝ) / 2, 1 / 2]
  norm_num at hsq
  have hnonneg : 0 ≤ κ / (20 * Real.sqrt 2) := by positivity
  nlinarith [sirsGradientBound_sq κ,
    norm_nonneg (sirsRadiusGradient κ !₂[(1 : ℝ) / 2, 1 / 2])]

/-- An attained maximum, so the upper bound is the exact supremum. -/
theorem sirsRadiusGradient_norm_isGreatest (κ : ℝ) (hκ : 0 ≤ κ) :
    IsGreatest ((fun p => ‖gradient (sirsRadius κ) p‖) '' sirsSimplex)
      (κ / (20 * Real.sqrt 2)) := by
  constructor
  · refine ⟨!₂[(1 : ℝ) / 2, 1 / 2], ?_, ?_⟩
    · norm_num [sirsSimplex]
    · simpa only [gradient_sirsRadius] using sirsRadiusGradient_norm_attained κ hκ
  · rintro value ⟨p, hp, rfl⟩
    simpa only [gradient_sirsRadius] using sirsRadiusGradient_norm_le κ hκ p hp

theorem sSup_norm_gradient_sirsRadius (κ : ℝ) (hκ : 0 ≤ κ) :
    sSup ((fun p => ‖gradient (sirsRadius κ) p‖) '' sirsSimplex) =
      (κ / 10) / (2 * Real.sqrt 2) := by
  rw [(sirsRadiusGradient_norm_isGreatest κ hκ).csSup_eq]
  ring

theorem sirsRadius_gradient_contraction (κ : ℝ) (hκ : 0 ≤ κ)
    (hthreshold : κ < 20 * Real.sqrt 2) (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ sirsSimplex) : ‖gradient (sirsRadius κ) p‖ < 1 := by
  rw [gradient_sirsRadius]
  apply lt_of_le_of_lt (sirsRadiusGradient_norm_le κ hκ p hp)
  exact (div_lt_one (by positivity : 0 < 20 * Real.sqrt (2 : ℝ))).mpr hthreshold

theorem sirs_numeric_threshold : (2828 : ℝ) / 100 < 20 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

theorem sirs_parameter_three_contraction (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ sirsSimplex) : ‖gradient (sirsRadius 3) p‖ < 1 :=
  sirsRadius_gradient_contraction 3 (by norm_num)
    (lt_trans (by norm_num : (3 : ℝ) < 2828 / 100) sirs_numeric_threshold) p hp

end BoundedUncertainty
