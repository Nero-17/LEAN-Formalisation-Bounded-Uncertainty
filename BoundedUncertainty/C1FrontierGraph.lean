import BoundedUncertainty.C1BoundaryGraph
import BoundedUncertainty.C1FrontierTopology
import Mathlib.Topology.TietzeExtension

/-!
A frontier-only C1 graph is converted to a one-sided domain graph for a
regular closed set. The input contains no side choice and no normal. A
continuous extension is used only to straighten the graph topologically;
all differentiability conclusions use the original local C1 function.
-/

namespace BoundedUncertainty

open Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A C1 hypersurface description of the frontier, with no domain side specified. -/
structure C1FrontierGraphAt (B : Set E) (y : E) where
  coordinates : E ≃L[ℝ] ℝ × F
  neighborhood : Set E
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : y ∈ neighborhood
  graphDomain : Set F
  isOpen_graphDomain : IsOpen graphDomain
  zero_mem_graphDomain : (0 : F) ∈ graphDomain
  graph : F → ℝ
  contDiffOn_graph : ContDiffOn ℝ 1 graph graphDomain
  graph_zero : graph 0 = 0
  mem_frontier_iff : ∀ z ∈ neighborhood,
    z ∈ frontier B ↔ (coordinates (z - y)).1 = graph (coordinates (z - y)).2

omit [NormedSpace ℝ F] in
theorem exists_continuous_extension_near_zero (graph : F → ℝ) (domain : Set F)
    (hdomain : IsOpen domain) (hzero : (0 : F) ∈ domain)
    (hgraph : ContinuousOn graph domain) :
    ∃ extension : C(F, ℝ), ∃ radius : ℝ, 0 < radius ∧
      Metric.ball 0 radius ⊆ domain ∧ Set.EqOn extension graph (Metric.ball 0 radius) := by
  obtain ⟨radius, hradius, hball⟩ := Metric.isOpen_iff.mp hdomain 0 hzero
  have hclosedBall : Metric.closedBall (0 : F) (radius / 2) ⊆ domain := by
    intro z hz
    apply hball
    exact Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
  obtain ⟨extension, hextension⟩ :=
    (⟨fun z : Metric.closedBall (0 : F) (radius / 2) => graph z,
      (hgraph.mono hclosedBall).restrict⟩ : C(Metric.closedBall (0 : F) (radius / 2), ℝ)).exists_restrict_eq
      Metric.isClosed_closedBall
  refine ⟨extension, radius / 2, by linarith, ?_, ?_⟩
  · exact Metric.ball_subset_closedBall.trans hclosedBall
  · intro z hz
    exact congrArg (fun f : C(Metric.closedBall (0 : F) (radius / 2), ℝ) =>
      f ⟨z, Metric.ball_subset_closedBall hz⟩) hextension

/-- The continuous shear used to straighten a local graph after continuous extension. -/
noncomputable def graphCoordinatesHomeomorph (coordinates : E ≃L[ℝ] ℝ × F) (y : E)
    (graph : C(F, ℝ)) : (ℝ × F) ≃ₜ E where
  toFun z := y + coordinates.symm (z.1 + graph z.2, z.2)
  invFun z := ((coordinates (z - y)).1 - graph (coordinates (z - y)).2,
    (coordinates (z - y)).2)
  left_inv z := by simp
  right_inv z := by
    dsimp
    simp only [sub_add_cancel]
    change y + coordinates.symm (coordinates (z - y)) = z
    simp
  continuous_toFun := continuous_const.add (coordinates.symm.continuous.comp
    ((continuous_fst.add (graph.continuous.comp continuous_snd)).prodMk continuous_snd))
  continuous_invFun :=
    (((coordinates.continuous.comp (continuous_id.sub continuous_const)).fst.sub
      (graph.continuous.comp
        (coordinates.continuous.comp (continuous_id.sub continuous_const)).snd)).prodMk
      (coordinates.continuous.comp (continuous_id.sub continuous_const)).snd)

@[simp] theorem graphCoordinatesHomeomorph_apply (coordinates : E ≃L[ℝ] ℝ × F)
    (y : E) (graph : C(F, ℝ)) (z : ℝ × F) :
    graphCoordinatesHomeomorph coordinates y graph z =
      y + coordinates.symm (z.1 + graph z.2, z.2) := rfl

@[simp] theorem graphCoordinatesHomeomorph_symm_apply (coordinates : E ≃L[ℝ] ℝ × F)
    (y : E) (graph : C(F, ℝ)) (z : E) :
    (graphCoordinatesHomeomorph coordinates y graph).symm z =
      ((coordinates (z - y)).1 - graph (coordinates (z - y)).2,
        (coordinates (z - y)).2) := rfl

variable {B : Set E} {y : E}

theorem C1FrontierGraphAt.mem_frontier (chart : C1FrontierGraphAt (F := F) B y) :
    y ∈ frontier B := by
  apply (chart.mem_frontier_iff y chart.mem_neighborhood).2
  simp [chart.graph_zero]

/-- Regular closedness forces a frontier graph to be a one-sided domain graph. -/
theorem C1FrontierGraphAt.nonempty_boundaryGraph (chart : C1FrontierGraphAt (F := F) B y)
    (hB : IsRegularClosed B) : Nonempty (C1BoundaryGraphAt (F := F) B y) := by
  obtain ⟨extension, radius, hradius, _, hagrees⟩ := exists_continuous_extension_near_zero
    chart.graph chart.graphDomain chart.isOpen_graphDomain chart.zero_mem_graphDomain
    chart.contDiffOn_graph.continuousOn
  have hextensionZero : extension 0 = 0 :=
    (hagrees (Metric.mem_ball_self hradius)).trans chart.graph_zero
  have hcoordinatesZero : graphCoordinatesHomeomorph chart.coordinates y extension 0 = y := by
    simp [hextensionZero]
  have hopen : IsOpen
      ((graphCoordinatesHomeomorph chart.coordinates y extension) ⁻¹' chart.neighborhood ∩
        (Prod.snd ⁻¹' Metric.ball (0 : F) radius)) :=
    (chart.isOpen_neighborhood.preimage
      (graphCoordinatesHomeomorph chart.coordinates y extension).continuous).inter
        (Metric.isOpen_ball.preimage continuous_snd)
  have hzero : (0 : ℝ × F) ∈
      ((graphCoordinatesHomeomorph chart.coordinates y extension) ⁻¹' chart.neighborhood ∩
        (Prod.snd ⁻¹' Metric.ball (0 : F) radius)) := by
    constructor
    · change graphCoordinatesHomeomorph chart.coordinates y extension 0 ∈ chart.neighborhood
      rw [hcoordinatesZero]
      exact chart.mem_neighborhood
    · exact Metric.mem_ball_self hradius
  obtain ⟨chartRadius, hchartRadius, hchartBall⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  have hfrontier : ∀ z ∈ Metric.ball (0 : ℝ × F) chartRadius,
      z ∈ frontier ((graphCoordinatesHomeomorph chart.coordinates y extension) ⁻¹' B) ↔
        z.1 = 0 := by
    intro z hz
    rw [← (graphCoordinatesHomeomorph chart.coordinates y extension).preimage_frontier]
    change graphCoordinatesHomeomorph chart.coordinates y extension z ∈ frontier B ↔ _
    rw [chart.mem_frontier_iff _ (hchartBall hz).1]
    simp only [graphCoordinatesHomeomorph_apply, add_sub_cancel_left,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [hagrees (hchartBall hz).2]
    exact add_eq_right
  have hagreesInverse : ∀ z,
      (graphCoordinatesHomeomorph chart.coordinates y extension).symm z ∈
        Metric.ball (0 : ℝ × F) chartRadius →
      extension (chart.coordinates (z - y)).2 = chart.graph (chart.coordinates (z - y)).2 := by
    intro z hz
    exact hagrees (hchartBall hz).2
  rcases one_sided_of_frontier_flat
      ((graphCoordinatesHomeomorph chart.coordinates y extension) ⁻¹' B)
      (hB.preimage_homeomorph (graphCoordinatesHomeomorph chart.coordinates y extension))
      chartRadius hchartRadius hfrontier with hnegative | hpositive
  · refine ⟨{
      coordinates := chart.coordinates
      neighborhood := (graphCoordinatesHomeomorph chart.coordinates y extension).symm ⁻¹'
        Metric.ball 0 chartRadius
      isOpen_neighborhood := Metric.isOpen_ball.preimage
        (graphCoordinatesHomeomorph chart.coordinates y extension).symm.continuous
      mem_neighborhood := ?_
      graphDomain := chart.graphDomain
      isOpen_graphDomain := chart.isOpen_graphDomain
      zero_mem_graphDomain := chart.zero_mem_graphDomain
      graph := chart.graph
      contDiffOn_graph := chart.contDiffOn_graph
      graph_zero := chart.graph_zero
      mem_iff := ?_ }⟩
    · change (graphCoordinatesHomeomorph chart.coordinates y extension).symm y ∈
        Metric.ball (0 : ℝ × F) chartRadius
      simpa [hextensionZero] using
        (Metric.mem_ball_self hchartRadius : (0 : ℝ × F) ∈ Metric.ball 0 chartRadius)
    · intro z hz
      have hside := hnegative ((graphCoordinatesHomeomorph chart.coordinates y extension).symm z) hz
      simp only [Set.mem_preimage, Homeomorph.apply_symm_apply] at hside
      simpa only [graphCoordinatesHomeomorph_symm_apply, hagreesInverse z hz, sub_nonpos] using hside
  · refine ⟨{
      coordinates := chart.coordinates.trans
        ((ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ F))
      neighborhood := (graphCoordinatesHomeomorph chart.coordinates y extension).symm ⁻¹'
        Metric.ball 0 chartRadius
      isOpen_neighborhood := Metric.isOpen_ball.preimage
        (graphCoordinatesHomeomorph chart.coordinates y extension).symm.continuous
      mem_neighborhood := ?_
      graphDomain := chart.graphDomain
      isOpen_graphDomain := chart.isOpen_graphDomain
      zero_mem_graphDomain := chart.zero_mem_graphDomain
      graph := fun z => -chart.graph z
      contDiffOn_graph := chart.contDiffOn_graph.neg
      graph_zero := by simp [chart.graph_zero]
      mem_iff := ?_ }⟩
    · change (graphCoordinatesHomeomorph chart.coordinates y extension).symm y ∈
        Metric.ball (0 : ℝ × F) chartRadius
      simpa [hextensionZero] using
        (Metric.mem_ball_self hchartRadius : (0 : ℝ × F) ∈ Metric.ball 0 chartRadius)
    · intro z hz
      have hside := hpositive ((graphCoordinatesHomeomorph chart.coordinates y extension).symm z) hz
      simp only [Set.mem_preimage, Homeomorph.apply_symm_apply] at hside
      simpa only [graphCoordinatesHomeomorph_symm_apply, hagreesInverse z hz, sub_nonneg,
        ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.neg_apply, ContinuousLinearEquiv.refl_apply,
        neg_le_neg_iff] using hside

noncomputable def C1FrontierGraphAt.toC1BoundaryGraphAt
    (chart : C1FrontierGraphAt (F := F) B y) (hB : IsRegularClosed B) :
    C1BoundaryGraphAt (F := F) B y :=
  (chart.nonempty_boundaryGraph hB).some

variable [CompleteSpace E]

/-- The actual normalized boundary witness follows from a frontier-only hypersurface chart. -/
noncomputable def C1FrontierGraphAt.toC1BoundaryAt
    (chart : C1FrontierGraphAt (F := F) B y) (hB : IsRegularClosed B) : C1BoundaryAt B y :=
  (chart.toC1BoundaryGraphAt hB).toC1BoundaryAt

end BoundedUncertainty
