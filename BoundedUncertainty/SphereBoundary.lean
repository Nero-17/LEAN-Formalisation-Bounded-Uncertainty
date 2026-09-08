import BoundedUncertainty.LocalBoundary
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The outward C1 boundary data of a positive-radius ball

The defining function is the squared distance from the centre minus the squared
radius. It is smooth on the whole ambient space. The normalization in
`C1BoundaryAt.ofDefiningFunction` gives the outward radial unit normal.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasGradientAt_sqDist_sub_sqRadius (y z : E) (R : ℝ) :
    HasGradientAt (fun w : E => ‖w - y‖ ^ 2 - R ^ 2) ((2 : ℝ) • (z - y)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((hasFDerivAt_id z).sub_const y).norm_sq.sub_const (R ^ 2)) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
theorem mem_closedBall_iff_sqDist_sub_sqRadius_nonpos (y w : E) (R : ℝ) (hR : 0 ≤ R) :
    w ∈ Metric.closedBall y R ↔ ‖w - y‖ ^ 2 - R ^ 2 ≤ 0 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  constructor <;> intro h <;> nlinarith [norm_nonneg (w - y)]

/-- Explicit regular-level-set data for a ball at a point on its sphere. -/
noncomputable def C1BoundaryAt.closedBall (y : E) (R : ℝ) (z : E)
    (hR : 0 < R) (hz : z ∈ Metric.sphere y R) : C1BoundaryAt (Metric.closedBall y R) z := by
  have hnorm : ‖z - y‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  have hnonzero : z - y ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    exact (ne_of_gt hR) hnorm.symm
  refine C1BoundaryAt.ofDefiningFunction (Metric.closedBall y R) z
    Set.univ isOpen_univ (Set.mem_univ z) (fun w : E => ‖w - y‖ ^ 2 - R ^ 2)
    ?_ ?_ ?_ ((2 : ℝ) • (z - y))
    (hasGradientAt_sqDist_sub_sqRadius y z R) (smul_ne_zero (by norm_num) hnonzero)
  · exact (((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).contDiffOn
  · change ‖z - y‖ ^ 2 - R ^ 2 = 0
    rw [hnorm, sub_self]
  · intro w _
    exact mem_closedBall_iff_sqDist_sub_sqRadius_nonpos y w R hR.le

theorem C1BoundaryAt.closedBall_normal (y : E) (R : ℝ) (z : E)
    (hR : 0 < R) (hz : z ∈ Metric.sphere y R) :
    (C1BoundaryAt.closedBall y R z hR hz).normal = ‖z - y‖⁻¹ • (z - y) := by
  change ‖(2 : ℝ) • (z - y)‖⁻¹ • ((2 : ℝ) • (z - y)) = ‖z - y‖⁻¹ • (z - y)
  rw [norm_smul, Real.norm_ofNat, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), mul_one]

theorem C1BoundaryAt.closedBall_normal_eq_inv_radius_smul (y : E) (R : ℝ) (z : E)
    (hR : 0 < R) (hz : z ∈ Metric.sphere y R) :
    (C1BoundaryAt.closedBall y R z hR hz).normal = R⁻¹ • (z - y) := by
  rw [C1BoundaryAt.closedBall_normal]
  have hnorm : ‖z - y‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  rw [hnorm]

end BoundedUncertainty
