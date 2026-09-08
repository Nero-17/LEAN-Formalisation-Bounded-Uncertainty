import BoundedUncertainty.LocalNormalGraph
import BoundedUncertainty.NormalCoordinates
import BoundedUncertainty.C1FrontierGraph
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-! A normal-secant criterion for an actual regular closed frontier.
Unlike the standalone arbitrary-manifold criterion, this proof obtains
projection openness from the two sides of the regular closed set. -/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Continuous nonzero normal covectors and two-point flatness produce an
unoriented C1 frontier chart, without assuming the frontier is a graph. -/
theorem nonempty_c1FrontierGraphAt_of_normal_chords {B : Set E}
    (hB : IsRegularClosed B) (normal : E → E →L[ℝ] ℝ)
    (hcontinuous : ContinuousOn normal (frontier B))
    (hsecants : ∀ point ∈ frontier B,
      (fun pair : E × E => normal point (pair.2 - pair.1))
        =o[𝓝[frontier B ×ˢ frontier B] (point, point)] (fun pair => pair.2 - pair.1))
    (point : E) (hpoint : point ∈ frontier B) (transverse : E)
    (htransverse : normal point transverse = 1) :
    Nonempty (C1FrontierGraphAt (F := (normal point).ker) B point) := by
  let coordinates := normalCoordinates (normal point) transverse htransverse
  let homeomorph : (ℝ × (normal point).ker) ≃ₜ E :=
    { toFun := fun value => point + coordinates.symm value
      invFun := fun value => coordinates (value - point)
      left_inv := by intro value; simp
      right_inv := by intro value; simp
      continuous_toFun := continuous_const.add coordinates.symm.continuous
      continuous_invFun := coordinates.continuous.comp (continuous_id.sub continuous_const) }
  have hzero : homeomorph 0 = point := by change point + coordinates.symm 0 = point; simp
  have hdifference (first second : ℝ × (normal point).ker) :
      homeomorph second - homeomorph first = coordinates.symm (second - first) := by
    change (point + coordinates.symm second) - (point + coordinates.symm first) = _
    rw [map_sub]
    abel
  have hnormalCoordinate (value : ℝ × (normal point).ker) :
      normal point (coordinates.symm value) = value.1 := by
    have h := normalCoordinates_fst (normal point) transverse htransverse (coordinates.symm value)
    change (coordinates (coordinates.symm value)).1 = _ at h
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h.symm
  let coordinateSet := homeomorph ⁻¹' B
  have hregular : IsRegularClosed coordinateSet := hB.preimage_homeomorph homeomorph
  have hfrontier : frontier coordinateSet = homeomorph ⁻¹' frontier B :=
    homeomorph.preimage_frontier B |>.symm
  have hzeroFrontier : (0 : ℝ × (normal point).ker) ∈ frontier coordinateSet := by
    rw [hfrontier]
    change homeomorph 0 ∈ frontier B
    rwa [hzero]
  have hmaps : MapsTo homeomorph (frontier coordinateSet) (frontier B) := by
    intro value hvalue
    change value ∈ homeomorph ⁻¹' frontier B
    rwa [← hfrontier]
  have hpairMaps : MapsTo (fun pair => (homeomorph pair.1, homeomorph pair.2))
      (frontier coordinateSet ×ˢ frontier coordinateSet) (frontier B ×ˢ frontier B) :=
    fun _ hpair => ⟨hmaps hpair.1, hmaps hpair.2⟩
  have hpairTendsto (value : ℝ × (normal point).ker) :
      Tendsto (fun pair => (homeomorph pair.1, homeomorph pair.2))
        (𝓝[frontier coordinateSet ×ˢ frontier coordinateSet] (value, value))
        (𝓝[frontier B ×ˢ frontier B] (homeomorph value, homeomorph value)) :=
    ((homeomorph.continuous.comp continuous_fst).prodMk
      (homeomorph.continuous.comp continuous_snd)).continuousWithinAt.tendsto_nhdsWithin hpairMaps
  have hflat : (fun pair : (ℝ × (normal point).ker) × (ℝ × (normal point).ker) =>
      pair.2.1 - pair.1.1)
      =o[𝓝[frontier coordinateSet ×ˢ frontier coordinateSet] (0, 0)]
        (fun pair => pair.2 - pair.1) := by
    have h := (hsecants point hpoint).comp_tendsto (hzero ▸ hpairTendsto 0)
    have hrewritten : (fun pair => normal point (coordinates.symm (pair.2 - pair.1)))
        =o[𝓝[frontier coordinateSet ×ˢ frontier coordinateSet] (0, 0)]
          (fun pair => coordinates.symm (pair.2 - pair.1)) := by
      simpa only [Function.comp_def, hdifference] using h
    simpa only [hnormalCoordinate, Prod.fst_sub] using
      hrewritten.trans_isBigO (coordinates.symm.isBigO_comp
        (fun pair : (ℝ × (normal point).ker) × (ℝ × (normal point).ker) => pair.2 - pair.1) _)
  let covector : (ℝ × (normal point).ker) → (ℝ × (normal point).ker) →L[ℝ] ℝ :=
    fun value => (normal (homeomorph value)).comp coordinates.symm.toContinuousLinearMap
  have hcovector : ContinuousOn covector (frontier coordinateSet) :=
    (hcontinuous.comp homeomorph.continuous.continuousOn hmaps).clm_comp continuousOn_const
  let horizontal := fun value => (covector value).comp (ContinuousLinearMap.inr ℝ ℝ (normal point).ker)
  let vertical := fun value => covector value (1, 0)
  have hvertical : vertical 0 = 1 := by
    change normal (homeomorph 0) (coordinates.symm (1, 0)) = 1
    rw [hzero, hnormalCoordinate]
  have hdecompose (value first second : ℝ × (normal point).ker) :
      vertical value * (second.1 - first.1) + horizontal value (second.2 - first.2) =
        normal (homeomorph value) (homeomorph second - homeomorph first) := by
    rw [hdifference]
    change covector value (1, 0) * (second.1 - first.1) +
      covector value (0, second.2 - first.2) = covector value (second - first)
    have hsplit : second - first = (second.1 - first.1) • (1, 0) + (0, second.2 - first.2) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, smul_eq_mul]
    ring
  have hsingle (value : ℝ × (normal point).ker) (hvalue : value ∈ frontier coordinateSet) :
      (fun other => vertical value * (other.1 - value.1) + horizontal value (other.2 - value.2))
        =o[𝓝[frontier coordinateSet] value] (fun other => other - value) := by
    have htendsto : Tendsto (fun other => (value, other)) (𝓝[frontier coordinateSet] value)
        (𝓝[frontier coordinateSet ×ˢ frontier coordinateSet] (value, value)) :=
      (continuous_const.prodMk continuous_id).continuousWithinAt.tendsto_nhdsWithin
        (fun _ hother => ⟨hvalue, hother⟩)
    have h := ((hsecants (homeomorph value) (hmaps hvalue)).comp_tendsto
      (hpairTendsto value)).comp_tendsto htendsto
    have hrewritten : (fun other => vertical value * (other.1 - value.1) +
        horizontal value (other.2 - value.2)) =o[𝓝[frontier coordinateSet] value]
        (fun other => coordinates.symm (other - value)) := by
      simpa only [Function.comp_def, hdecompose, hdifference] using h
    exact hrewritten.trans_isBigO (coordinates.symm.isBigO_sub _ value)
  obtain ⟨height, hheight, radius, hradius, graph, hgraphZero, hgraphSmooth, hgraphFrontier⟩ :=
    exists_c1_frontier_graph_of_local_normal_chords hregular hzeroFrontier hflat horizontal vertical
      (hcovector.clm_comp continuousOn_const) (hcovector.clm_apply continuousOn_const)
      (by rw [hvertical]; norm_num) hsingle
  refine ⟨{
    coordinates := coordinates
    neighborhood := (fun value => coordinates (value - point)) ⁻¹'
      (Ioo (-height) height ×ˢ Metric.ball (0 : (normal point).ker) radius)
    isOpen_neighborhood := (isOpen_Ioo.prod Metric.isOpen_ball).preimage
      (coordinates.continuous.comp (continuous_id.sub continuous_const))
    mem_neighborhood := by
      change coordinates (point - point) ∈ Ioo (-height) height ×ˢ
        Metric.ball (0 : (normal point).ker) radius
      simp only [sub_self, map_zero]
      exact ⟨⟨neg_neg_of_pos hheight, hheight⟩, Metric.mem_ball_self hradius⟩
    graphDomain := Metric.ball 0 radius
    isOpen_graphDomain := Metric.isOpen_ball
    zero_mem_graphDomain := Metric.mem_ball_self hradius
    graph := graph
    contDiffOn_graph := hgraphSmooth
    graph_zero := hgraphZero
    mem_frontier_iff := ?_ }⟩
  intro value hvalue
  have hcoordinateMem : coordinates (value - point) ∈
      Icc (-height) height ×ˢ Metric.ball (0 : (normal point).ker) radius :=
    ⟨⟨hvalue.1.1.le, hvalue.1.2.le⟩, hvalue.2⟩
  have h := hgraphFrontier _ hcoordinateMem
  rw [hfrontier] at h
  change homeomorph (coordinates (value - point)) ∈ frontier B ↔ _ at h
  have heq : homeomorph (coordinates (value - point)) = value := by
    change point + coordinates.symm (coordinates (value - point)) = value
    simp
  simpa only [heq] using h

end BoundedUncertainty
