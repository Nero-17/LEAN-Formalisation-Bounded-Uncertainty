import BoundedUncertainty.C1FrontierTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
An elementary open-projection criterion for a regular closed frontier.
This uses the two sides of an actual frontier, not invariance of domain for
an arbitrary topological manifold.
-/

namespace BoundedUncertainty

open Set Topology
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- A vertical interval joining opposite sides crosses the frontier internally. -/
theorem exists_vertical_frontier_between {B : Set (ℝ × F)} (hB : IsClosed B)
    {lower upper : ℝ} {horizontal : F} (hlt : lower < upper)
    (hsides : ((lower, horizontal) ∈ interior B ∧ (upper, horizontal) ∉ B) ∨
      ((lower, horizontal) ∉ B ∧ (upper, horizontal) ∈ interior B)) :
    ∃ height ∈ Ioo lower upper, (height, horizontal) ∈ frontier B := by
  have hconnected : IsPreconnected ((fun height : ℝ => (height, horizontal)) ''
      Icc lower upper) :=
    isPreconnected_Icc.image _ (continuous_id.prodMk continuous_const).continuousOn
  have hexists : ∃ height ∈ Icc lower upper, (height, horizontal) ∈ frontier B := by
    by_contra! hnone
    have hside := isPreconnected_subset_interior_or_compl hB hconnected (by
      rintro _ ⟨height, hheight, rfl⟩
      exact hnone height hheight)
    have hl : (lower, horizontal) ∈ (fun height : ℝ => (height, horizontal)) ''
        Icc lower upper := ⟨lower, ⟨le_rfl, hlt.le⟩, rfl⟩
    have hu : (upper, horizontal) ∈ (fun height : ℝ => (height, horizontal)) ''
        Icc lower upper := ⟨upper, ⟨hlt.le, le_rfl⟩, rfl⟩
    rcases hsides with hsides | hsides <;> rcases hside with hside | hside
    · exact hsides.2 (interior_subset (hside hu))
    · exact hside hl (interior_subset hsides.1)
    · exact hsides.1 (interior_subset (hside hl))
    · exact hside hu (interior_subset hsides.2)
  obtain ⟨height, hheight, hfrontier⟩ := hexists
  have hlne : height ≠ lower := by
    intro heq
    subst height
    rcases hsides with hsides | hsides
    · exact hfrontier.2 hsides.1
    · exact hsides.1 (hB.frontier_subset hfrontier)
  have hune : height ≠ upper := by
    intro heq
    subst height
    rcases hsides with hsides | hsides
    · exact hsides.2 (hB.frontier_subset hfrontier)
    · exact hfrontier.2 hsides.2
  exact ⟨height, ⟨lt_of_le_of_ne hheight.1 hlne.symm,
    lt_of_le_of_ne hheight.2 hune⟩, hfrontier⟩

/-- A frontier with at most one point on each vertical fibre projects onto an
open horizontal ball, provided the top and bottom caps avoid the frontier.
Regular closedness rules out an isolated sheet with no interior side. -/
theorem frontier_projects_onto_ball {B : Set (ℝ × F)} (hB : IsRegularClosed B)
    (hzero : (0 : ℝ × F) ∈ frontier B) {height radius : ℝ}
    (hheight : 0 < height) (hradius : 0 < radius)
    (hcaps : ∀ horizontal ∈ Metric.ball (0 : F) radius,
      (-height, horizontal) ∉ frontier B ∧ (height, horizontal) ∉ frontier B)
    (hunique : ∀ horizontal ∈ Metric.ball (0 : F) radius,
      ∀ lower ∈ Icc (-height) height, ∀ upper ∈ Icc (-height) height,
        (lower, horizontal) ∈ frontier B → (upper, horizontal) ∈ frontier B →
        lower = upper) :
    ∀ horizontal ∈ Metric.ball (0 : F) radius,
      ∃! value, value ∈ Ioo (-height) height ∧ (value, horizontal) ∈ frontier B := by
  have hnegative := isPreconnected_subset_interior_or_compl hB.isClosed
    ((convex_ball (0 : F) radius).isPreconnected.image (fun horizontal : F => (-height, horizontal))
      (continuous_const.prodMk continuous_id).continuousOn)
    (by rintro _ ⟨horizontal, hhorizontal, rfl⟩; exact (hcaps horizontal hhorizontal).1)
  have hpositive := isPreconnected_subset_interior_or_compl hB.isClosed
    ((convex_ball (0 : F) radius).isPreconnected.image (fun horizontal : F => (height, horizontal))
      (continuous_const.prodMk continuous_id).continuousOn)
    (by rintro _ ⟨horizontal, hhorizontal, rfl⟩; exact (hcaps horizontal hhorizontal).2)
  have hwindowOpen : IsOpen (Ioo (-height) height ×ˢ Metric.ball (0 : F) radius) :=
    isOpen_Ioo.prod Metric.isOpen_ball
  have hzeroWindow : (0 : ℝ × F) ∈ Ioo (-height) height ×ˢ Metric.ball (0 : F) radius :=
    ⟨⟨neg_neg_of_pos hheight, hheight⟩, Metric.mem_ball_self hradius⟩
  have hnotBothExterior
      (hnegative : (fun horizontal : F => (-height, horizontal)) ''
        Metric.ball 0 radius ⊆ Bᶜ)
      (hpositive : (fun horizontal : F => (height, horizontal)) ''
        Metric.ball 0 radius ⊆ Bᶜ) : False := by
    have hzeroClosure : (0 : ℝ × F) ∈ closure (interior B) := by
      rw [hB]
      exact hB.isClosed.frontier_subset hzero
    obtain ⟨point, hpointWindow, hpointInterior⟩ := mem_closure_iff_nhds.mp hzeroClosure
      _ (hwindowOpen.mem_nhds hzeroWindow)
    obtain ⟨lower, hlower, hlowerFrontier⟩ := exists_vertical_frontier_between hB.isClosed
      hpointWindow.1.1 (Or.inr ⟨hnegative ⟨point.2, hpointWindow.2, rfl⟩,
        hpointInterior⟩)
    obtain ⟨upper, hupper, hupperFrontier⟩ := exists_vertical_frontier_between hB.isClosed
      hpointWindow.1.2 (Or.inl ⟨hpointInterior,
        hpositive ⟨point.2, hpointWindow.2, rfl⟩⟩)
    have heq := hunique point.2 hpointWindow.2 lower
      ⟨hlower.1.le, (hlower.2.trans hpointWindow.1.2).le⟩ upper
      ⟨(hpointWindow.1.1.trans hupper.1).le, hupper.2.le⟩
      hlowerFrontier hupperFrontier
    linarith [hlower.2, hupper.1]
  have hnotBothInterior
      (hnegative : (fun horizontal : F => (-height, horizontal)) ''
        Metric.ball 0 radius ⊆ interior B)
      (hpositive : (fun horizontal : F => (height, horizontal)) ''
        Metric.ball 0 radius ⊆ interior B) : False := by
    have hexterior : ∃ point ∈ Ioo (-height) height ×ˢ Metric.ball (0 : F) radius,
        point ∉ B := by
      by_contra! hnone
      exact hzero.2 (interior_maximal hnone hwindowOpen hzeroWindow)
    obtain ⟨point, hpointWindow, hpointExterior⟩ := hexterior
    obtain ⟨lower, hlower, hlowerFrontier⟩ := exists_vertical_frontier_between hB.isClosed
      hpointWindow.1.1 (Or.inl ⟨hnegative ⟨point.2, hpointWindow.2, rfl⟩,
        hpointExterior⟩)
    obtain ⟨upper, hupper, hupperFrontier⟩ := exists_vertical_frontier_between hB.isClosed
      hpointWindow.1.2 (Or.inr ⟨hpointExterior,
        hpositive ⟨point.2, hpointWindow.2, rfl⟩⟩)
    have heq := hunique point.2 hpointWindow.2 lower
      ⟨hlower.1.le, (hlower.2.trans hpointWindow.1.2).le⟩ upper
      ⟨(hpointWindow.1.1.trans hupper.1).le, hupper.2.le⟩
      hlowerFrontier hupperFrontier
    linarith [hlower.2, hupper.1]
  have hsides : ∀ horizontal ∈ Metric.ball (0 : F) radius,
      ((-height, horizontal) ∈ interior B ∧ (height, horizontal) ∉ B) ∨
      ((-height, horizontal) ∉ B ∧ (height, horizontal) ∈ interior B) := by
    rcases hnegative with hnegative | hnegative <;>
      rcases hpositive with hpositive | hpositive
    · exact (hnotBothInterior hnegative hpositive).elim
    · intro horizontal hhorizontal
      exact Or.inl ⟨hnegative ⟨horizontal, hhorizontal, rfl⟩,
        hpositive ⟨horizontal, hhorizontal, rfl⟩⟩
    · intro horizontal hhorizontal
      exact Or.inr ⟨hnegative ⟨horizontal, hhorizontal, rfl⟩,
        hpositive ⟨horizontal, hhorizontal, rfl⟩⟩
    · exact (hnotBothExterior hnegative hpositive).elim
  intro horizontal hhorizontal
  obtain ⟨value, hvalue, hfrontier⟩ := exists_vertical_frontier_between hB.isClosed
    (by linarith : -height < height) (hsides horizontal hhorizontal)
  refine ⟨value, ⟨hvalue, hfrontier⟩, ?_⟩
  intro other hother
  exact hunique horizontal hhorizontal other ⟨hother.1.1.le, hother.1.2.le⟩ value
    ⟨hvalue.1.le, hvalue.2.le⟩ hother.2 hfrontier

/-- A two-point cone estimate gives a Lipschitz graph on an open ball.
Projection openness and the existence of the graph are conclusions. -/
theorem exists_lipschitz_frontier_graph_of_cone {B : Set (ℝ × F)}
    (hB : IsRegularClosed B) (hzero : (0 : ℝ × F) ∈ frontier B)
    {height radius : ℝ} (hheight : 0 < height) (hradius : 0 < radius)
    (constant : ℝ≥0) (hscale : (constant : ℝ) * radius < height)
    (hcone : ∀ point ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
      ∀ other ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
        point ∈ frontier B → other ∈ frontier B →
        |point.1 - other.1| ≤ constant * ‖point.2 - other.2‖) :
    ∃ graph : F → ℝ, graph 0 = 0 ∧
      LipschitzOnWith constant graph (Metric.ball 0 radius) ∧
      (∀ horizontal ∈ Metric.ball (0 : F) radius, graph horizontal ∈ Ioo (-height) height) ∧
      ∀ point ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
        point ∈ frontier B ↔ point.1 = graph point.2 := by
  classical
  have hzeroCylinder : (0 : ℝ × F) ∈
      Icc (-height) height ×ˢ Metric.ball (0 : F) radius :=
    ⟨⟨(neg_neg_of_pos hheight).le, hheight.le⟩, Metric.mem_ball_self hradius⟩
  have hcap (value : ℝ) (hvalue : value ∈ Icc (-height) height)
      (habs : |value| = height) (horizontal : F)
      (hhorizontal : horizontal ∈ Metric.ball (0 : F) radius) :
      (value, horizontal) ∉ frontier B := by
    intro hfrontier
    have hbound := hcone (value, horizontal) ⟨hvalue, hhorizontal⟩ 0 hzeroCylinder
      hfrontier hzero
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at hbound
    rw [habs] at hbound
    have hnorm : ‖horizontal‖ < radius := by simpa [dist_zero_right] using hhorizontal
    have hmul := mul_le_mul_of_nonneg_left hnorm.le constant.coe_nonneg
    exact (not_lt_of_ge (hbound.trans hmul)) hscale
  have hunique : ∀ horizontal ∈ Metric.ball (0 : F) radius,
      ∀ lower ∈ Icc (-height) height, ∀ upper ∈ Icc (-height) height,
        (lower, horizontal) ∈ frontier B → (upper, horizontal) ∈ frontier B →
        lower = upper := by
    intro horizontal hhorizontal lower hlower upper hupper hlowerFrontier hupperFrontier
    have hbound := hcone (lower, horizontal) ⟨hlower, hhorizontal⟩
      (upper, horizontal) ⟨hupper, hhorizontal⟩ hlowerFrontier hupperFrontier
    simpa only [sub_self, norm_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] using hbound
  have hexists := frontier_projects_onto_ball hB hzero hheight hradius (by
    intro horizontal hhorizontal
    exact ⟨hcap (-height) ⟨le_rfl, by linarith⟩
      (by rw [abs_neg, abs_of_pos hheight]) horizontal hhorizontal,
      hcap height ⟨by linarith, le_rfl⟩ (abs_of_pos hheight) horizontal hhorizontal⟩) hunique
  let graph : F → ℝ := fun horizontal =>
    if hhorizontal : horizontal ∈ Metric.ball (0 : F) radius then
      (hexists horizontal hhorizontal).choose else 0
  have hgraph (horizontal : F) (hhorizontal : horizontal ∈ Metric.ball (0 : F) radius) :
      graph horizontal ∈ Ioo (-height) height ∧ (graph horizontal, horizontal) ∈ frontier B := by
    simpa only [graph, dif_pos hhorizontal] using
      (hexists horizontal hhorizontal).choose_spec.1
  have hzeroGraph := hunique 0 (Metric.mem_ball_self hradius) (graph 0)
    ⟨(hgraph 0 (Metric.mem_ball_self hradius)).1.1.le,
      (hgraph 0 (Metric.mem_ball_self hradius)).1.2.le⟩ 0 hzeroCylinder.1
    (hgraph 0 (Metric.mem_ball_self hradius)).2 hzero
  refine ⟨graph, hzeroGraph, ?_, fun horizontal hhorizontal => (hgraph horizontal hhorizontal).1, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro horizontal hhorizontal other hother
    have hfirst := hgraph horizontal hhorizontal
    have hsecond := hgraph other hother
    have hbound := hcone (graph horizontal, horizontal)
      ⟨⟨hfirst.1.1.le, hfirst.1.2.le⟩, hhorizontal⟩ (graph other, other)
      ⟨⟨hsecond.1.1.le, hsecond.1.2.le⟩, hother⟩ hfirst.2 hsecond.2
    simpa only [Real.dist_eq, dist_eq_norm] using hbound
  · intro point hpoint
    constructor
    · intro hfrontier
      exact hunique point.2 hpoint.2 point.1 hpoint.1 (graph point.2)
        ⟨(hgraph point.2 hpoint.2).1.1.le, (hgraph point.2 hpoint.2).1.2.le⟩
        hfrontier (hgraph point.2 hpoint.2).2
    · intro heq
      have hpair : point = (graph point.2, point.2) := Prod.ext heq rfl
      rw [hpair]
      exact (hgraph point.2 hpoint.2).2

end BoundedUncertainty
