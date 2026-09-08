import BoundedUncertainty.GraphSecantRegularity
import BoundedUncertainty.DistinctSecants

/-!
Conditional graph assembly for an arbitrary subset. Projection openness is
an explicit hypothesis; none of the conclusions below proves that topological
step. `StandaloneManifoldCriterion` discharges it for topological manifolds.
The subset is not replaced by a regular closed frontier.
-/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local C1 hypersurface graph describing the subset itself. -/
structure C1HypersurfaceGraphAt (subset : Set E) (point : E) where
  coordinates : E ≃L[ℝ] ℝ × F
  neighborhood : Set E
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : point ∈ neighborhood
  graphDomain : Set F
  isOpen_graphDomain : IsOpen graphDomain
  zero_mem_graphDomain : (0 : F) ∈ graphDomain
  graph : F → ℝ
  contDiffOn_graph : ContDiffOn ℝ 1 graph graphDomain
  graph_zero : graph 0 = 0
  graph_mem : ∀ horizontal ∈ graphDomain,
    point + coordinates.symm (graph horizontal, horizontal) ∈ subset
  horizontal_mem : ∀ other ∈ neighborhood, (coordinates (other - point)).2 ∈ graphDomain
  mem_iff : ∀ other ∈ neighborhood,
    other ∈ subset ↔ (coordinates (other - point)).1 = graph (coordinates (other - point)).2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A cone gives a Lipschitz inverse of the horizontal projection on its image.
The image need not yet be open. -/
theorem exists_lipschitz_graph_of_cone {subset neighborhood : Set (ℝ × F)}
    (hzero : (0 : ℝ × F) ∈ subset ∩ neighborhood) (constant : ℝ≥0)
    (hcone : ∀ first ∈ subset ∩ neighborhood, ∀ second ∈ subset ∩ neighborhood,
      |first.1 - second.1| ≤ constant * ‖first.2 - second.2‖) :
    ∃ graph : F → ℝ, graph 0 = 0 ∧
      LipschitzOnWith constant graph (Prod.snd '' (subset ∩ neighborhood)) ∧
      (∀ horizontal ∈ Prod.snd '' (subset ∩ neighborhood),
        (graph horizontal, horizontal) ∈ subset ∩ neighborhood) ∧
      (∀ other ∈ neighborhood, other.2 ∈ Prod.snd '' (subset ∩ neighborhood) →
        (other ∈ subset ↔ other.1 = graph other.2)) := by
  classical
  let graph : F → ℝ := fun horizontal =>
    if hhorizontal : horizontal ∈ Prod.snd '' (subset ∩ neighborhood)
      then (Classical.choose hhorizontal).1 else 0
  have hgraph (horizontal : F) (hhorizontal : horizontal ∈ Prod.snd '' (subset ∩ neighborhood)) :
      (graph horizontal, horizontal) ∈ subset ∩ neighborhood := by
    have hchosen := Classical.choose_spec hhorizontal
    have hequal : (graph horizontal, horizontal) = Classical.choose hhorizontal :=
      Prod.ext (by simp only [graph, dif_pos hhorizontal]) hchosen.2.symm
    rw [hequal]
    exact hchosen.1
  have hsame (first second : ℝ × F) (hfirst : first ∈ subset ∩ neighborhood)
      (hsecond : second ∈ subset ∩ neighborhood) (hequal : first.2 = second.2) :
      first.1 = second.1 := by
    have h := hcone first hfirst second hsecond
    rw [hequal, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  have hzeroImage : (0 : F) ∈ Prod.snd '' (subset ∩ neighborhood) := ⟨0, hzero, rfl⟩
  refine ⟨graph, (hsame _ _ (hgraph 0 hzeroImage) hzero rfl), ?_, hgraph, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    simpa only [Real.dist_eq, dist_eq_norm] using
      hcone _ (hgraph first hfirst) _ (hgraph second hsecond)
  · intro other hother himage
    constructor
    · intro hmember
      exact hsame other _ ⟨hmember, hother⟩
        (hgraph other.2 ⟨other, ⟨hmember, hother⟩, rfl⟩) rfl
    · intro hequal
      have hmember := (hgraph other.2 himage).1
      simpa only [← hequal, Prod.mk.eta] using hmember

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Conditional analytic graph assembly. The open projection image is an
explicit topological premise, while C1 regularity follows from chord flatness. -/
theorem exists_c1_graph_of_cone_and_open_projection
    {subset neighborhood : Set (ℝ × F)}
    (hzero : (0 : ℝ × F) ∈ subset ∩ neighborhood)
    (hprojection : IsOpen (Prod.snd '' (subset ∩ neighborhood)))
    (constant : ℝ≥0)
    (hcone : ∀ first ∈ subset ∩ neighborhood, ∀ second ∈ subset ∩ neighborhood,
      |first.1 - second.1| ≤ constant * ‖first.2 - second.2‖)
    (horizontal : (ℝ × F) → F →L[ℝ] ℝ) (vertical : (ℝ × F) → ℝ)
    (hhorizontal : ContinuousOn horizontal (subset ∩ neighborhood))
    (hvertical : ContinuousOn vertical (subset ∩ neighborhood))
    (hnonzero : ∀ point ∈ subset ∩ neighborhood, vertical point ≠ 0)
    (hsecant : ∀ point ∈ subset ∩ neighborhood,
      (fun other => vertical point * (other.1 - point.1) + horizontal point (other.2 - point.2))
        =o[𝓝[subset] point] (fun other => other - point)) :
    ∃ graph : F → ℝ, graph 0 = 0 ∧
      ContDiffOn ℝ 1 graph (Prod.snd '' (subset ∩ neighborhood)) ∧
      (∀ point ∈ Prod.snd '' (subset ∩ neighborhood),
        (graph point, point) ∈ subset ∩ neighborhood) ∧
      (∀ other ∈ neighborhood, other.2 ∈ Prod.snd '' (subset ∩ neighborhood) →
        (other ∈ subset ↔ other.1 = graph other.2)) ∧
      (∀ point ∈ Prod.snd '' (subset ∩ neighborhood),
        HasFDerivAt graph
          ((-(vertical (graph point, point))⁻¹) • horizontal (graph point, point)) point) := by
  obtain ⟨graph, hgraphZero, hgraphLipschitz, hgraphMember, hgraphSubset⟩ :=
    exists_lipschitz_graph_of_cone hzero constant hcone
  have hgraphMap : MapsTo (fun point => (graph point, point))
      (Prod.snd '' (subset ∩ neighborhood)) (subset ∩ neighborhood) := hgraphMember
  have hgraphContinuous : ContinuousOn (fun point => (graph point, point))
      (Prod.snd '' (subset ∩ neighborhood)) :=
    hgraphLipschitz.continuousOn.prodMk continuousOn_id
  have hgraphSecant (point : F) (hpoint : point ∈ Prod.snd '' (subset ∩ neighborhood)) :
      (fun other => vertical (graph point, point) * (graph other - graph point) +
        horizontal (graph point, point) (other - point))
        =o[𝓝 point] (fun other => (graph other - graph point, other - point)) := by
    have htendsto : Tendsto (fun other => (graph other, other)) (𝓝 point)
        (𝓝[subset] (graph point, point)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hgraphContinuous.continuousAt (hprojection.mem_nhds hpoint), ?_⟩
      filter_upwards [hprojection.mem_nhds hpoint] with other hother
      exact (hgraphMember other hother).1
    simpa only [Function.comp_def, Prod.mk_sub_mk] using
      (hsecant _ (hgraphMember point hpoint)).comp_tendsto htendsto
  refine ⟨graph, hgraphZero, ?_, hgraphMember, hgraphSubset, ?_⟩
  · exact contDiffOn_graph_of_littleO_normal_chord hprojection hgraphLipschitz
      (fun point => horizontal (graph point, point)) (fun point => vertical (graph point, point))
      (hhorizontal.comp hgraphContinuous hgraphMap)
      (hvertical.comp hgraphContinuous hgraphMap)
      (fun point hpoint => hnonzero _ (hgraphMember point hpoint)) hgraphSecant
  · intro point hpoint
    exact hasFDerivAt_graph_of_littleO_normal_chord (hprojection.mem_nhds hpoint)
      hgraphLipschitz _ _ (hnonzero _ (hgraphMember point hpoint)) (hgraphSecant point hpoint)

end BoundedUncertainty
