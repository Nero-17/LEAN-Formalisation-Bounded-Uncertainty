import BoundedUncertainty.GraphSecantRegularity

/-! A two-moving-point little-o condition produces the local cone needed
by the actual-frontier graph criterion. No local graph is assumed. -/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- Uniform smallness of vertical secants supplies a cylinder with a cone bound. -/
theorem exists_cone_cylinder_of_littleO_vertical_chord {B : Set (ℝ × F)}
    (hsecant : (fun pair : (ℝ × F) × (ℝ × F) => pair.2.1 - pair.1.1)
      =o[𝓝[frontier B ×ˢ frontier B] (0, 0)] (fun pair => pair.2 - pair.1)) :
    ∃ height > 0, ∃ radius > 0, radius < height ∧
      ∀ point ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
        ∀ other ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
          point ∈ frontier B → other ∈ frontier B →
          |point.1 - other.1| ≤ ‖point.2 - other.2‖ := by
  obtain ⟨size, hsize, hbound⟩ := Metric.mem_nhdsWithin_iff.mp
    (hsecant.def (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨size / 2, by positivity, size / 4, by positivity, by linarith, ?_⟩
  have hnorm (point : ℝ × F)
      (hpoint : point ∈ Icc (-(size / 2)) (size / 2) ×ˢ Metric.ball (0 : F) (size / 4)) :
      ‖point‖ < size := by
    rw [Prod.norm_def, max_lt_iff, Real.norm_eq_abs]
    refine ⟨(abs_le.mpr hpoint.1).trans_lt (by linarith), ?_⟩
    have hhorizontal : ‖point.2‖ < size / 4 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hpoint.2
    linarith
  intro point hpoint other hother hpointFrontier hotherFrontier
  have hpair : (point, other) ∈ Metric.ball (0, 0) size := by
    rw [Metric.mem_ball, show ((0 : ℝ × F), (0 : ℝ × F)) = 0 from rfl,
      dist_zero_right, Prod.norm_def, max_lt_iff]
    exact ⟨hnorm point hpoint, hnorm other hother⟩
  have hsmall := hbound ⟨hpair, ⟨hpointFrontier, hotherFrontier⟩⟩
  change ‖other.1 - point.1‖ ≤ 1 / 2 * ‖other - point‖ at hsmall
  rw [Prod.norm_def, Real.norm_eq_abs] at hsmall
  simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs] at hsmall
  rw [abs_sub_comm, norm_sub_rev] at hsmall
  by_cases hle : |point.1 - other.1| ≤ ‖point.2 - other.2‖
  · exact hle
  · rw [max_eq_left (le_of_not_ge hle)] at hsmall
    nlinarith [abs_nonneg (point.1 - other.1), norm_nonneg (point.2 - other.2)]

end BoundedUncertainty
