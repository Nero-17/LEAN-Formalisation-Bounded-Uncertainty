import BoundedUncertainty.SecantCone

/-! A coordinate version of the full actual-frontier regularity criterion.
The local cone and transversality neighbourhood are both derived. -/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normal chord flatness at every frontier point gives a genuine local C1 graph,
when the coordinates at the marked point are adapted to its normal. -/
theorem exists_c1_frontier_graph_of_local_normal_chords {B : Set (ℝ × F)}
    (hB : IsRegularClosed B) (hzero : (0 : ℝ × F) ∈ frontier B)
    (hflat : (fun pair : (ℝ × F) × (ℝ × F) => pair.2.1 - pair.1.1)
      =o[𝓝[frontier B ×ˢ frontier B] (0, 0)] (fun pair => pair.2 - pair.1))
    (horizontal : (ℝ × F) → F →L[ℝ] ℝ) (vertical : (ℝ × F) → ℝ)
    (hhorizontal : ContinuousOn horizontal (frontier B))
    (hvertical : ContinuousOn vertical (frontier B)) (hnonzero : vertical 0 ≠ 0)
    (hsecant : ∀ point ∈ frontier B,
      (fun other => vertical point * (other.1 - point.1) + horizontal point (other.2 - point.2))
        =o[𝓝[frontier B] point] (fun other => other - point)) :
    ∃ height > 0, ∃ radius > 0, ∃ graph : F → ℝ,
      graph 0 = 0 ∧ ContDiffOn ℝ 1 graph (Metric.ball 0 radius) ∧
      ∀ point ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
        point ∈ frontier B ↔ point.1 = graph point.2 := by
  obtain ⟨height, hheight, radius, hradius, _, hcone⟩ :=
    exists_cone_cylinder_of_littleO_vertical_chord hflat
  have htransverse : ∀ᶠ point in 𝓝[frontier B] (0 : ℝ × F), vertical point ≠ 0 :=
    (hvertical 0 hzero).eventually (isOpen_compl_singleton.mem_nhds hnonzero)
  obtain ⟨size, hsize, hsizeNonzero⟩ := Metric.mem_nhdsWithin_iff.mp htransverse
  have hnewHeight : 0 < min height (size / 2) := lt_min hheight (by positivity)
  have hnewRadius : 0 < min radius (min height (size / 2) / 2) :=
    lt_min hradius (by positivity)
  have hheightLe := min_le_left height (size / 2)
  have hsizeLe := min_le_right height (size / 2)
  have hradiusLe := min_le_left radius (min height (size / 2) / 2)
  have hhalfLe := min_le_right radius (min height (size / 2) / 2)
  have hcylinder (point : ℝ × F)
      (hpoint : point ∈ Icc (-min height (size / 2)) (min height (size / 2)) ×ˢ
        Metric.ball (0 : F) (min radius (min height (size / 2) / 2))) :
      point ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius := by
    refine ⟨⟨?_, hpoint.1.2.trans hheightLe⟩, Metric.ball_subset_ball hradiusLe hpoint.2⟩
    linarith [hpoint.1.1]
  have hball (point : ℝ × F)
      (hpoint : point ∈ Icc (-min height (size / 2)) (min height (size / 2)) ×ˢ
        Metric.ball (0 : F) (min radius (min height (size / 2) / 2))) :
      point ∈ Metric.ball (0 : ℝ × F) size := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_lt_iff]
    have habs := abs_le.mpr hpoint.1
    have hnorm : ‖point.2‖ < min radius (min height (size / 2) / 2) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hpoint.2
    constructor <;> linarith
  obtain ⟨graph, hgraphZero, hgraphSmooth, hgraphFrontier⟩ :=
    exists_c1_frontier_graph_of_cone_and_normal_chords hB hzero hnewHeight hnewRadius 1
      (by change 1 * _ < _; linarith)
      (by
        intro point hpoint other hother hpointFrontier hotherFrontier
        simpa only [NNReal.coe_one, one_mul] using
          hcone point (hcylinder point hpoint) other (hcylinder other hother)
            hpointFrontier hotherFrontier)
      horizontal vertical (hhorizontal.mono inter_subset_right)
      (hvertical.mono inter_subset_right)
      (fun point hpoint => hsizeNonzero ⟨hball point hpoint.1, hpoint.2⟩)
      (fun point hpoint => hsecant point hpoint.2)
  exact ⟨_, hnewHeight, _, hnewRadius, graph, hgraphZero, hgraphSmooth, hgraphFrontier⟩

end BoundedUncertainty
