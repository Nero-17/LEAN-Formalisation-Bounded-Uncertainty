import BoundedUncertainty.FrontierProjection
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
The analytic part of the secant criterion. A Lipschitz graph whose ambient
chords are asymptotically annihilated by a transverse covector has the
corresponding derivative. Continuous covectors give a C1 graph.
-/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ambient normal flatness implies the derivative of a Lipschitz graph. -/
theorem hasFDerivAt_graph_of_littleO_normal_chord {graph : F → ℝ} {domain : Set F}
    {point : F} (hdomain : domain ∈ 𝓝 point) {constant : ℝ≥0}
    (hgraph : LipschitzOnWith constant graph domain)
    (horizontal : F →L[ℝ] ℝ) (vertical : ℝ) (hvertical : vertical ≠ 0)
    (hsecant : (fun other => vertical * (graph other - graph point) + horizontal (other - point))
      =o[𝓝 point] (fun other => (graph other - graph point, other - point))) :
    HasFDerivAt graph ((-vertical⁻¹) • horizontal) point := by
  have hpoint : point ∈ domain := mem_of_mem_nhds hdomain
  have hchord : (fun other => (graph other - graph point, other - point))
      =O[𝓝 point] (fun other => other - point) := by
    apply IsBigO.of_bound ((constant : ℝ) + 1)
    filter_upwards [hdomain] with other hother
    have hbound : ‖graph other - graph point‖ ≤ constant * ‖other - point‖ := by
      simpa only [dist_eq_norm] using hgraph.dist_le_mul other hother point hpoint
    rw [Prod.norm_def]
    apply max_le
    · nlinarith [norm_nonneg (other - point)]
    · nlinarith [norm_nonneg (other - point), constant.coe_nonneg]
  have hremainder := (hsecant.trans_isBigO hchord).const_mul_left vertical⁻¹
  rw [HasFDerivAt, hasFDerivAtFilter_iff_isLittleO]
  apply hremainder.congr_left
  intro other
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Continuous transverse normal covectors upgrade a Lipschitz graph to C1. -/
theorem contDiffOn_graph_of_littleO_normal_chord {graph : F → ℝ} {domain : Set F}
    (hdomain : IsOpen domain) {constant : ℝ≥0}
    (hgraph : LipschitzOnWith constant graph domain)
    (horizontal : F → F →L[ℝ] ℝ) (vertical : F → ℝ)
    (hhorizontal : ContinuousOn horizontal domain) (hvertical : ContinuousOn vertical domain)
    (hnonzero : ∀ point ∈ domain, vertical point ≠ 0)
    (hsecant : ∀ point ∈ domain,
      (fun other => vertical point * (graph other - graph point) + horizontal point (other - point))
        =o[𝓝 point] (fun other => (graph other - graph point, other - point))) :
    ContDiffOn ℝ 1 graph domain := by
  have hderivative : ContinuousOn (fun point => (-(vertical point)⁻¹) • horizontal point) domain :=
    (hvertical.inv₀ hnonzero).neg.smul hhorizontal
  intro point hpoint
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_one_iff]
  exact ⟨_, domain, hdomain.mem_nhds hpoint, hderivative, fun other hother =>
    hasFDerivAt_graph_of_littleO_normal_chord (hdomain.mem_nhds hother) hgraph
      (horizontal other) (vertical other) (hnonzero other hother) (hsecant other hother)⟩

/-- The frontier itself supplies the graph and its C1 regularity. The cone
condition is local, and normal flatness is imposed on actual frontier chords. -/
theorem exists_c1_frontier_graph_of_cone_and_normal_chords {B : Set (ℝ × F)}
    (hB : IsRegularClosed B) (hzero : (0 : ℝ × F) ∈ frontier B)
    {height radius : ℝ} (hheight : 0 < height) (hradius : 0 < radius)
    (constant : ℝ≥0) (hscale : (constant : ℝ) * radius < height)
    (hcone : ∀ point ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
      ∀ other ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
        point ∈ frontier B → other ∈ frontier B →
        |point.1 - other.1| ≤ constant * ‖point.2 - other.2‖)
    (horizontal : (ℝ × F) → F →L[ℝ] ℝ) (vertical : (ℝ × F) → ℝ)
    (hhorizontal : ContinuousOn horizontal
      ((Icc (-height) height ×ˢ Metric.ball (0 : F) radius) ∩ frontier B))
    (hvertical : ContinuousOn vertical
      ((Icc (-height) height ×ˢ Metric.ball (0 : F) radius) ∩ frontier B))
    (hnonzero : ∀ point ∈ (Icc (-height) height ×ˢ Metric.ball (0 : F) radius) ∩ frontier B,
      vertical point ≠ 0)
    (hsecant : ∀ point ∈ (Icc (-height) height ×ˢ Metric.ball (0 : F) radius) ∩ frontier B,
      (fun other => vertical point * (other.1 - point.1) + horizontal point (other.2 - point.2))
        =o[𝓝[frontier B] point] (fun other => other - point)) :
    ∃ graph : F → ℝ, graph 0 = 0 ∧ ContDiffOn ℝ 1 graph (Metric.ball 0 radius) ∧
      ∀ point ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius,
        point ∈ frontier B ↔ point.1 = graph point.2 := by
  obtain ⟨graph, hgraphZero, hgraphLipschitz, hgraphRange, hgraphFrontier⟩ :=
    exists_lipschitz_frontier_graph_of_cone hB hzero hheight hradius constant hscale hcone
  have hgraphCylinder (point : F) (hpoint : point ∈ Metric.ball (0 : F) radius) :
      (graph point, point) ∈ Icc (-height) height ×ˢ Metric.ball (0 : F) radius :=
    ⟨⟨(hgraphRange point hpoint).1.le, (hgraphRange point hpoint).2.le⟩, hpoint⟩
  have hgraphMember (point : F) (hpoint : point ∈ Metric.ball (0 : F) radius) :
      (graph point, point) ∈ frontier B :=
    (hgraphFrontier _ (hgraphCylinder point hpoint)).2 rfl
  have hgraphMap : MapsTo (fun point => (graph point, point)) (Metric.ball (0 : F) radius)
      ((Icc (-height) height ×ˢ Metric.ball (0 : F) radius) ∩ frontier B) :=
    fun point hpoint => ⟨hgraphCylinder point hpoint, hgraphMember point hpoint⟩
  have hgraphContinuous : ContinuousOn (fun point => (graph point, point))
      (Metric.ball (0 : F) radius) := hgraphLipschitz.continuousOn.prodMk continuousOn_id
  refine ⟨graph, hgraphZero, ?_, hgraphFrontier⟩
  apply contDiffOn_graph_of_littleO_normal_chord Metric.isOpen_ball hgraphLipschitz
    (fun point => horizontal (graph point, point)) (fun point => vertical (graph point, point))
    (hhorizontal.comp hgraphContinuous hgraphMap) (hvertical.comp hgraphContinuous hgraphMap)
    (fun point hpoint => hnonzero _ (hgraphMap hpoint))
  intro point hpoint
  have htendsto : Tendsto (fun other => (graph other, other)) (𝓝 point)
      (𝓝[frontier B] (graph point, point)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hgraphContinuous.continuousAt (Metric.isOpen_ball.mem_nhds hpoint), ?_⟩
    filter_upwards [Metric.isOpen_ball.mem_nhds hpoint] with other hother
    exact hgraphMember other hother
  simpa only [Function.comp_def, Prod.mk_sub_mk] using
    (hsecant _ (hgraphMap hpoint)).comp_tendsto htendsto

end BoundedUncertainty
