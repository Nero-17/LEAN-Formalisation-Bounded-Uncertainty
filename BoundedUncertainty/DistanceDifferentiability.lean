import BoundedUncertainty.NearestPointContinuity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
Differentiability of distance to a compact set at an exterior point with a
unique nearest point. The squared-distance sandwich is proved first and uses
only convergence of nearby minimizers, not differentiability of a projection.
-/

namespace BoundedUncertainty

open Set Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two nearest-point inequalities control the full squared-distance remainder. -/
theorem sqDist_remainder_bound (y x w z : E)
    (hbase : ‖y - x‖ ≤ ‖y - z‖) (hnear : ‖w - z‖ ≤ ‖w - x‖) :
    |‖w - z‖ ^ 2 - ‖y - x‖ ^ 2 - 2 * inner ℝ (y - x) (w - y)| ≤
      (‖w - y‖ + 2 * ‖z - x‖) * ‖w - y‖ := by
  have hupper := norm_add_sq_real (y - x) (w - y)
  have hupperVector : y - x + (w - y) = w - x := by abel
  rw [hupperVector] at hupper
  have hlower := norm_add_sq_real (y - z) (w - y)
  have hlowerVector : y - z + (w - y) = w - z := by abel
  rw [hlowerVector] at hlower
  have hdecomposition : y - z = (y - x) + (x - z) := by abel
  have hinnerDecomposition : inner ℝ (y - z) (w - y) =
      inner ℝ (y - x) (w - y) + inner ℝ (x - z) (w - y) := by
    rw [hdecomposition, inner_add_left]
  rw [hinnerDecomposition] at hlower
  have hinner := neg_le_of_abs_le (abs_real_inner_le_norm (x - z) (w - y))
  rw [norm_sub_rev x z] at hinner
  have hupperBound :
      ‖w - z‖ ^ 2 - ‖y - x‖ ^ 2 - 2 * inner ℝ (y - x) (w - y) ≤ ‖w - y‖ ^ 2 := by
    nlinarith [norm_nonneg (w - z), norm_nonneg (w - x)]
  have hlowerBound : -(2 * ‖z - x‖ * ‖w - y‖) ≤
      ‖w - z‖ ^ 2 - ‖y - x‖ ^ 2 - 2 * inner ℝ (y - x) (w - y) := by
    nlinarith [norm_nonneg (y - x), norm_nonneg (y - z), sq_nonneg ‖w - y‖]
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg ‖w - y‖]
  · nlinarith [mul_nonneg (norm_nonneg (z - x)) (norm_nonneg (w - y))]

/-- A quantitative error estimate for the actual squared infimum distance. -/
theorem infDist_sq_remainder_bound (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y x : E) (hx : x ∈ A)
    (hnearest : dist y x = Metric.infDist y A) (w : E) :
    |Metric.infDist w A ^ 2 - Metric.infDist y A ^ 2 - 2 * inner ℝ (y - x) (w - y)| ≤
      (‖w - y‖ + 2 * ‖compactNearestPoint A hcompact hnonempty w - x‖) * ‖w - y‖ := by
  have hbase : ‖y - x‖ ≤ ‖y - compactNearestPoint A hcompact hnonempty w‖ := by
    simpa only [dist_eq_norm] using hnearest.trans_le
      (Metric.infDist_le_dist_of_mem (compactNearestPoint_mem A hcompact hnonempty w))
  have hnear : ‖w - compactNearestPoint A hcompact hnonempty w‖ ≤ ‖w - x‖ := by
    simpa only [dist_eq_norm] using (dist_compactNearestPoint A hcompact hnonempty w).trans_le
      (Metric.infDist_le_dist_of_mem hx)
  have hresult := sqDist_remainder_bound y x w (compactNearestPoint A hcompact hnonempty w) hbase hnear
  rw [← dist_eq_norm, dist_compactNearestPoint, ← dist_eq_norm, hnearest] at hresult
  exact hresult

variable [CompleteSpace E]

/-- The squared distance has the expected derivative from uniqueness only at the marked point. -/
theorem hasGradientAt_infDist_sq_of_unique_nearest (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y x : E) (hx : x ∈ A)
    (hnearest : dist y x = Metric.infDist y A)
    (hunique : ∀ z ∈ A, dist y z = Metric.infDist y A → z = x) :
    HasGradientAt (fun w : E => Metric.infDist w A ^ 2) ((2 : ℝ) • (y - x)) y := by
  have hprojection := tendsto_compactNearestPoint_of_unique A hcompact hnonempty y x hx hnearest hunique
  have hsmall : Tendsto
      (fun w : E => ‖w - y‖ + 2 * ‖compactNearestPoint A hcompact hnonempty w - x‖)
      (𝓝 y) (𝓝 0) := by
    simpa using ((continuous_id.tendsto y).sub_const y).norm.add
      (((hprojection.sub_const x).norm).const_mul 2)
  rw [hasGradientAt_iff_hasFDerivAt, HasFDerivAt, hasFDerivAtFilter_iff_isLittleO]
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hsmall.eventually (Iio_mem_nhds hc)] with w hw
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left, Real.norm_eq_abs]
  exact (infDist_sq_remainder_bound A hcompact hnonempty y x hx hnearest w).trans
    (mul_le_mul_of_nonneg_right hw.le (norm_nonneg (w - y)))

/-- The actual distance gradient at an exterior point with a unique nearest point. -/
theorem hasGradientAt_infDist_of_unique_nearest (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y x : E) (hx : x ∈ A) (hy : y ∉ A)
    (hnearest : dist y x = Metric.infDist y A)
    (hunique : ∀ z ∈ A, dist y z = Metric.infDist y A → z = x) :
    HasGradientAt (fun w : E => Metric.infDist w A) (‖y - x‖⁻¹ • (y - x)) y := by
  have hnorm : ‖y - x‖ ≠ 0 := by
    intro hzero
    exact hy ((sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm ▸ hx)
  have hdistance : Metric.infDist y A ≠ 0 := by
    rw [← hnearest, dist_eq_norm]
    exact hnorm
  have hsquared := hasGradientAt_infDist_sq_of_unique_nearest A hcompact hnonempty y x hx hnearest hunique
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hsquared.hasFDerivAt.sqrt (pow_ne_zero 2 hdistance) using 1
  · funext w
    exact (Real.sqrt_sq (Metric.infDist_nonneg : 0 ≤ Metric.infDist w A)).symm
  · ext v
    simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
      real_inner_smul_left, smul_eq_mul, Real.sqrt_sq Metric.infDist_nonneg]
    rw [← hnearest, dist_eq_norm]
    field_simp

end BoundedUncertainty
