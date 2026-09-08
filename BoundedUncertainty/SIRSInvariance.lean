import BoundedUncertainty.SIRSGeometry
import BoundedUncertainty.SIRSGradient
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.RieszLemma

/-! Radius-distance estimates and actual closed-ball invariance for the SIRS state space. -/
namespace BoundedUncertainty
open Set Metric

theorem sirsRadius_eq_zero_of_mem_frontier (κ : ℝ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ frontier sirsSimplex) : sirsRadius κ p = 0 := by
  rcases (mem_frontier_sirsSimplex p).mp hp with ⟨_, hzero | hzero | hzero⟩
  · simp [sirsRadius, hzero]
  · simp [sirsRadius, hzero]
  · have hlast : 1 - p 0 - p 1 = 0 := by linarith
    simp [sirsRadius, hlast]

theorem sirsRadius_lipschitz_estimate (κ : ℝ) (hκ : 0 ≤ κ)
    (p q : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) (hq : q ∈ sirsSimplex) :
    ‖sirsRadius κ p - sirsRadius κ q‖ ≤ (κ / (20 * Real.sqrt 2)) * dist p q := by
  have hderivative : ∀ x ∈ sirsSimplex, HasFDerivWithinAt (sirsRadius κ)
      (InnerProductSpace.toDual ℝ _ (sirsRadiusGradient κ x)) sirsSimplex x :=
    fun x _ => (hasGradientAt_sirsRadius κ x).hasFDerivAt.hasFDerivWithinAt
  have hbound : ∀ x ∈ sirsSimplex,
      ‖InnerProductSpace.toDual ℝ _ (sirsRadiusGradient κ x)‖ ≤ κ / (20 * Real.sqrt 2) := by
    intro x hx
    rw [(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).norm_map]
    exact sirsRadiusGradient_norm_le κ hκ x hx
  simpa only [dist_eq_norm] using
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderivative hbound convex_sirsSimplex hq hp

theorem sirsRadius_le_gradientBound_mul_infDist_compl (κ : ℝ) (hκ : 0 ≤ κ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    sirsRadius κ p ≤ (κ / (20 * Real.sqrt 2)) * infDist p sirsSimplexᶜ := by
  obtain ⟨q, hq, hdist⟩ := isCompact_sirsSimplex.exists_mem_frontier_infDist_compl_eq_dist hp
  have hbound := sirsRadius_lipschitz_estimate κ hκ p q hp
    (isClosed_sirsSimplex.frontier_subset hq)
  rw [sirsRadius_eq_zero_of_mem_frontier κ q hq, sub_zero,
    Real.norm_of_nonneg (sirsRadius_nonneg κ hκ p hp), ← hdist] at hbound
  exact hbound

theorem sirsRadius_le_gradientBound_mul_infDist_frontier (κ : ℝ) (hκ : 0 ≤ κ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    sirsRadius κ p ≤ (κ / (20 * Real.sqrt 2)) * infDist p (frontier sirsSimplex) := by
  have hnonempty : (frontier sirsSimplex).Nonempty :=
    ⟨0, (mem_frontier_sirsSimplex 0).mpr ⟨by norm_num [sirsSimplex], Or.inl (by simp)⟩⟩
  obtain ⟨q, hq, hdist⟩ := isClosed_frontier.exists_infDist_eq_dist hnonempty p
  have hbound := sirsRadius_lipschitz_estimate κ hκ p q hp
    (isClosed_sirsSimplex.frontier_subset hq)
  rw [sirsRadius_eq_zero_of_mem_frontier κ q hq, sub_zero,
    Real.norm_of_nonneg (sirsRadius_nonneg κ hκ p hp), ← hdist] at hbound
  exact hbound

theorem sirsRadius_lt_infDist_frontier_of_mem_interior (κ : ℝ) (hκ : 0 ≤ κ)
    (hthreshold : κ < 20 * Real.sqrt 2) (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ interior sirsSimplex) : sirsRadius κ p < infDist p (frontier sirsSimplex) := by
  have hnonempty : (frontier sirsSimplex).Nonempty :=
    ⟨0, (mem_frontier_sirsSimplex 0).mpr ⟨by norm_num [sirsSimplex], Or.inl (by simp)⟩⟩
  have hpositive : 0 < infDist p (frontier sirsSimplex) :=
    (isClosed_frontier.notMem_iff_infDist_pos hnonempty).mp
      (fun hfrontier => hfrontier.2 hp)
  have hfactor : κ / (20 * Real.sqrt 2) < 1 :=
    (div_lt_one (by positivity : 0 < 20 * Real.sqrt (2 : ℝ))).mpr hthreshold
  exact (sirsRadius_le_gradientBound_mul_infDist_frontier κ hκ p (interior_subset hp)).trans_lt
    (by nlinarith)

theorem sirs_closedBall_subset (κ : ℝ) (hκ : 0 ≤ κ)
    (hthreshold : κ < 20 * Real.sqrt 2) (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ sirsSimplex) : closedBall p (sirsRadius κ p) ⊆ sirsSimplex := by
  have hfactor : κ / (20 * Real.sqrt 2) ≤ 1 :=
    ((div_lt_one (by positivity : 0 < 20 * Real.sqrt (2 : ℝ))).mpr hthreshold).le
  have hradius : sirsRadius κ p ≤ infDist p sirsSimplexᶜ :=
    (sirsRadius_le_gradientBound_mul_infDist_compl κ hκ p hp).trans
      (by nlinarith [infDist_nonneg (x := p) (s := sirsSimplexᶜ)])
  exact (closedBall_subset_closedBall hradius).trans
    ((closedBall_infDist_compl_subset_closure hp).trans_eq isClosed_sirsSimplex.closure_eq)

theorem sirsRadius_le_bound (κ : ℝ) (hκ : 0 ≤ κ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) : sirsRadius κ p ≤ κ / 10 + 1 := by
  have hS : p 0 ≤ 1 := by linarith [hp.2.1, hp.2.2]
  have hI : p 1 ≤ 1 := by linarith [hp.1, hp.2.2]
  have hlast : 0 ≤ 1 - p 0 - p 1 := by linarith [hp.2.2]
  have hlastUpper : 1 - p 0 - p 1 ≤ 1 := by linarith [hp.1, hp.2.1]
  have hproduct : p 0 * p 1 * (1 - p 0 - p 1) ≤ 1 :=
    mul_le_one₀ (mul_le_one₀ hS hp.2.1 hI) hlast hlastUpper
  have hbound := mul_le_mul_of_nonneg_left hproduct (div_nonneg hκ (by norm_num : (0 : ℝ) ≤ 10))
  dsimp [sirsRadius]
  nlinarith

end BoundedUncertainty
