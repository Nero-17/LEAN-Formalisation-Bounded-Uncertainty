import BoundedUncertainty.DistanceDifferentiability
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
The closed-set version in a proper metric space follows by a proved compact
localization of the actual infimum distance. Only the marked nearest point
must be unique. No projection smoothness or nearby uniqueness is assumed.
-/

namespace BoundedUncertainty

open Set Filter Topology

section Metric

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- A closed set has the same actual distance as one compact truncation near the marked point. -/
theorem exists_compact_infDist_localization_of_isClosed (A : Set E) (hclosed : IsClosed A)
    (y x : E) (hx : x ∈ A) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ A ∧ x ∈ K ∧
      ∀ᶠ w in 𝓝 y, Metric.infDist w K = Metric.infDist w A := by
  have hxball : x ∈ Metric.closedBall y (dist y x + 2) := by
    change dist x y ≤ dist y x + 2
    rw [dist_comm x y]
    linarith
  refine ⟨A ∩ Metric.closedBall y (dist y x + 2),
    (isCompact_closedBall y (dist y x + 2)).inter_left hclosed,
    inter_subset_left, ⟨hx, hxball⟩, ?_⟩
  filter_upwards [Metric.ball_mem_nhds y zero_lt_one] with w hw
  obtain ⟨z, hz, hdist⟩ := hclosed.exists_infDist_eq_dist ⟨x, hx⟩ w
  have hnearest : dist w z ≤ dist w x :=
    hdist.symm.trans_le (Metric.infDist_le_dist_of_mem hx)
  have hzball : z ∈ Metric.closedBall y (dist y x + 2) := by
    change dist z y ≤ dist y x + 2
    have hfirst := dist_triangle z w y
    have hsecond := dist_triangle w y x
    rw [dist_comm z w] at hfirst
    change dist w y < 1 at hw
    linarith
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem (show z ∈ A ∩ Metric.closedBall y (dist y x + 2) from
      ⟨hz, hzball⟩)).trans_eq hdist.symm
  · exact Metric.infDist_le_infDist_of_subset inter_subset_left ⟨x, hx, hxball⟩

end Metric

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-- The squared distance formula for a closed set in a proper real inner-product space. -/
theorem hasGradientAt_infDist_sq_of_unique_nearest_of_isClosed (A : Set E) (hclosed : IsClosed A)
    (y x : E) (hx : x ∈ A) (hnearest : dist y x = Metric.infDist y A)
    (hunique : ∀ z ∈ A, dist y z = Metric.infDist y A → z = x) :
    HasGradientAt (fun w : E => Metric.infDist w A ^ 2) ((2 : ℝ) • (y - x)) y := by
  obtain ⟨K, hcompact, hsubset, hxK, hlocal⟩ :=
    exists_compact_infDist_localization_of_isClosed A hclosed y x hx
  have hvalue : Metric.infDist y K = Metric.infDist y A := hlocal.self_of_nhds
  apply (hasGradientAt_infDist_sq_of_unique_nearest K hcompact ⟨x, hxK⟩ y x hxK
    (hnearest.trans hvalue.symm)
    (fun z hz hdist => hunique z (hsubset hz) (hdist.trans hvalue))).congr_of_eventuallyEq
  filter_upwards [hlocal] with w hw
  exact congrArg (fun value : ℝ => value ^ 2) hw.symm

/-- The actual exterior distance gradient for a closed set, without convexity. -/
theorem hasGradientAt_infDist_of_unique_nearest_of_isClosed (A : Set E) (hclosed : IsClosed A)
    (y x : E) (hx : x ∈ A) (hy : y ∉ A) (hnearest : dist y x = Metric.infDist y A)
    (hunique : ∀ z ∈ A, dist y z = Metric.infDist y A → z = x) :
    HasGradientAt (fun w : E => Metric.infDist w A) (‖y - x‖⁻¹ • (y - x)) y := by
  obtain ⟨K, hcompact, hsubset, hxK, hlocal⟩ :=
    exists_compact_infDist_localization_of_isClosed A hclosed y x hx
  have hvalue : Metric.infDist y K = Metric.infDist y A := hlocal.self_of_nhds
  apply (hasGradientAt_infDist_of_unique_nearest K hcompact ⟨x, hxK⟩ y x hxK
    (fun hyK => hy (hsubset hyK)) (hnearest.trans hvalue.symm)
    (fun z hz hdist => hunique z (hsubset hz) (hdist.trans hvalue))).congr_of_eventuallyEq
  filter_upwards [hlocal] with w hw
  exact hw.symm

end InnerProduct

end BoundedUncertainty
