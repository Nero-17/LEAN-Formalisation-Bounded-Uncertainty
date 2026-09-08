import BoundedUncertainty.SphereBoundary

/-! First-order geometry of nonzero-gradient local maximizers for Theorem 4.10. -/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem not_mem_interior_of_isLocalMaxOn_hasGradientAt
    {A : Set E} {G : E → ℝ} {x gradient : E}
    (hmax : IsLocalMaxOn G A x) (hgradient : HasGradientAt G gradient x)
    (hnonzero : gradient ≠ 0) : x ∉ interior A := by
  intro hx
  have hzero := (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hx)).hasFDerivAt_eq_zero
    hgradient.hasFDerivAt
  apply hnonzero
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa only [map_zero] using hzero

/-- A nonzero maximizing gradient selects the outward normal, with positive orientation. -/
theorem C1BoundaryAt.normal_eq_normalized_gradient_of_isLocalMaxOn
    {A : Set E} {x : E} (boundary : C1BoundaryAt A x)
    (G : E → ℝ) (gradient : E) (hgradient : HasGradientAt G gradient x)
    (hnonzero : gradient ≠ 0) (hmax : IsLocalMaxOn G A x) :
    ‖gradient‖⁻¹ • gradient = boundary.normal := by
  obtain ⟨coefficient, hnonnegative, hmultiple⟩ :=
    boundary.exists_nonneg_smul_of_isLocalMaxOn G gradient hgradient hmax
  have hnorm : ‖gradient‖ = coefficient := by
    rw [hmultiple, norm_smul, Real.norm_of_nonneg hnonnegative, boundary.normal_unit, mul_one]
  calc
    ‖gradient‖⁻¹ • gradient = ‖gradient‖⁻¹ • (coefficient • boundary.normal) :=
      congrArg (fun v : E => ‖gradient‖⁻¹ • v) hmultiple
    _ = boundary.normal := by
      rw [smul_smul, ← hnorm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hnonzero), one_smul]

/-- A ball maximizer has the radial normalized gradient; zero radius is included. -/
theorem eq_center_add_radius_normalized_gradient_of_isLocalMaxOn_closedBall
    (center x : E) (radius : ℝ) (hradius : 0 ≤ radius)
    (hx : x ∈ Metric.closedBall center radius)
    (G : E → ℝ) (gradient : E) (hgradient : HasGradientAt G gradient x)
    (hnonzero : gradient ≠ 0) (hmax : IsLocalMaxOn G (Metric.closedBall center radius) x) :
    x = center + radius • (‖gradient‖⁻¹ • gradient) := by
  by_cases hzero : radius = 0
  · have hcenter : x = center := by simpa [hzero] using hx
    simp [hzero, hcenter]
  have hpositive : 0 < radius := lt_of_le_of_ne hradius (Ne.symm hzero)
  have hcontact : dist x center = radius := by
    apply le_antisymm hx
    apply le_of_not_gt
    intro hstrict
    exact not_mem_interior_of_isLocalMaxOn_hasGradientAt hmax hgradient hnonzero
      (interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball hstrict)
  have hnormal := (C1BoundaryAt.closedBall center radius x hpositive hcontact).normal_eq_normalized_gradient_of_isLocalMaxOn
    G gradient hgradient hnonzero hmax
  rw [C1BoundaryAt.closedBall_normal_eq_inv_radius_smul] at hnormal
  rw [hnormal, smul_smul, mul_inv_cancel₀ hzero, one_smul]
  simp

end BoundedUncertainty
