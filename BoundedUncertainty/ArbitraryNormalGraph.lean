import BoundedUncertainty.ArbitraryLocalGraph
import BoundedUncertainty.NormalCoordinates
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-!
The arbitrary-subset normal criterion, conditional on local projection
openness. Coordinates are adapted to the actual supplied normal. The resulting
graph describes the subset itself, and the normal annihilates every graph
tangent. No frontier, regular-closedness or pre-existing C1 graph is assumed.
`StandaloneManifoldCriterion` derives the open-projection premise for the
original topological manifold input.
-/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_c1HypersurfaceGraphAt_of_normal_chords_and_open_projection
    (subset : Set E) (normal : E → E →L[ℝ] ℝ)
    (hcontinuous : ContinuousOn normal subset)
    (hsecants : ∀ point ∈ subset,
      (fun pair : E × E => normal point (pair.2 - pair.1))
        =o[𝓝[subset ×ˢ subset] (point, point)] (fun pair => pair.2 - pair.1))
    (point : E) (hpoint : point ∈ subset) (transverse : E)
    (htransverse : normal point transverse = 1)
    (patch : Set E) (hpatch : IsOpen patch) (hpointPatch : point ∈ patch)
    (hprojection : IsOpenMap (fun value : ↥(subset ∩ patch) =>
      (normalCoordinates (normal point) transverse htransverse ((value : E) - point)).2)) :
    ∃ chart : C1HypersurfaceGraphAt (F := (normal point).ker) subset point,
      ∀ horizontal ∈ chart.graphDomain, ∀ tangent : (normal point).ker,
        normal (point + chart.coordinates.symm (chart.graph horizontal, horizontal))
          (chart.coordinates.symm (fderiv ℝ chart.graph horizontal tangent, tangent)) = 0 := by
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
  let coordinateSet := homeomorph ⁻¹' subset
  let coordinatePatch := homeomorph ⁻¹' patch
  have hzeroMember : (0 : ℝ × (normal point).ker) ∈ coordinateSet := by
    change homeomorph 0 ∈ subset
    rwa [hzero]
  have hzeroPatch : (0 : ℝ × (normal point).ker) ∈ coordinatePatch := by
    change homeomorph 0 ∈ patch
    rwa [hzero]
  have hmaps : MapsTo homeomorph coordinateSet subset := fun _ hvalue => hvalue
  have hpairMaps : MapsTo (fun pair => (homeomorph pair.1, homeomorph pair.2))
      (coordinateSet ×ˢ coordinateSet) (subset ×ˢ subset) :=
    fun _ hpair => ⟨hmaps hpair.1, hmaps hpair.2⟩
  have hpairTendsto (value : ℝ × (normal point).ker) :
      Tendsto (fun pair => (homeomorph pair.1, homeomorph pair.2))
        (𝓝[coordinateSet ×ˢ coordinateSet] (value, value))
        (𝓝[subset ×ˢ subset] (homeomorph value, homeomorph value)) :=
    ((homeomorph.continuous.comp continuous_fst).prodMk
      (homeomorph.continuous.comp continuous_snd)).continuousWithinAt.tendsto_nhdsWithin hpairMaps
  have hflat : (fun pair : (ℝ × (normal point).ker) × (ℝ × (normal point).ker) =>
      pair.2.1 - pair.1.1)
      =o[𝓝[coordinateSet ×ˢ coordinateSet] (0, 0)] (fun pair => pair.2 - pair.1) := by
    have h := (hsecants point hpoint).comp_tendsto (hzero ▸ hpairTendsto 0)
    have hrewritten : (fun pair => normal point (coordinates.symm (pair.2 - pair.1)))
        =o[𝓝[coordinateSet ×ˢ coordinateSet] (0, 0)]
          (fun pair => coordinates.symm (pair.2 - pair.1)) := by
      simpa only [Function.comp_def, hdifference] using h
    simpa only [hnormalCoordinate, Prod.fst_sub] using
      hrewritten.trans_isBigO (coordinates.symm.isBigO_comp
        (fun pair : (ℝ × (normal point).ker) × (ℝ × (normal point).ker) => pair.2 - pair.1) _)
  let covector : (ℝ × (normal point).ker) → (ℝ × (normal point).ker) →L[ℝ] ℝ :=
    fun value => (normal (homeomorph value)).comp coordinates.symm.toContinuousLinearMap
  have hcovector : ContinuousOn covector coordinateSet :=
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
  have hsingle (value : ℝ × (normal point).ker) (hvalue : value ∈ coordinateSet) :
      (fun other => vertical value * (other.1 - value.1) + horizontal value (other.2 - value.2))
        =o[𝓝[coordinateSet] value] (fun other => other - value) := by
    have htendsto : Tendsto (fun other => (value, other)) (𝓝[coordinateSet] value)
        (𝓝[coordinateSet ×ˢ coordinateSet] (value, value)) :=
      (continuous_const.prodMk continuous_id).continuousWithinAt.tendsto_nhdsWithin
        (fun _ hother => ⟨hvalue, hother⟩)
    have h := ((hsecants (homeomorph value) (hmaps hvalue)).comp_tendsto
      (hpairTendsto value)).comp_tendsto htendsto
    have hrewritten : (fun other => vertical value * (other.1 - value.1) +
        horizontal value (other.2 - value.2)) =o[𝓝[coordinateSet] value]
        (fun other => coordinates.symm (other - value)) := by
      simpa only [Function.comp_def, hdecompose, hdifference] using h
    exact hrewritten.trans_isBigO (coordinates.symm.isBigO_sub _ value)
  let subtypeHomeomorph : ↥(coordinateSet ∩ coordinatePatch) ≃ₜ ↥(subset ∩ patch) :=
    homeomorph.subtype (fun _ => Iff.rfl)
  have hprojectionCoordinates : IsOpenMap
      (fun value : ↥(coordinateSet ∩ coordinatePatch) => (value : ℝ × (normal point).ker).2) := by
    have h := hprojection.comp subtypeHomeomorph.isOpenMap
    convert h using 1
    funext value
    change (value : ℝ × (normal point).ker).2 = (coordinates (homeomorph value - point)).2
    simp [homeomorph]
  obtain ⟨neighborhood, hopen, hmem, domain, hdomain, hzeroDomain,
      graph, hgraphZero, hgraphSmooth, hgraphMember, hgraphSubset, hgraphHorizontal, hgraphNormal⟩ :=
    exists_c1_graph_of_local_normal_chords_and_open_projection hzeroMember
      (hpatch.preimage homeomorph.continuous) hzeroPatch hprojectionCoordinates hflat
      horizontal vertical (hcovector.clm_comp continuousOn_const)
      (hcovector.clm_apply continuousOn_const) (by rw [hvertical]; norm_num) hsingle
  refine ⟨{
    coordinates := coordinates
    neighborhood := (fun value => coordinates (value - point)) ⁻¹' neighborhood
    isOpen_neighborhood := hopen.preimage
      (coordinates.continuous.comp (continuous_id.sub continuous_const))
    mem_neighborhood := by simpa only [mem_preimage, sub_self, map_zero] using hmem
    graphDomain := domain
    isOpen_graphDomain := hdomain
    zero_mem_graphDomain := hzeroDomain
    graph := graph
    contDiffOn_graph := hgraphSmooth
    graph_zero := hgraphZero
    graph_mem := fun parameter hparameter => hgraphMember parameter hparameter
    horizontal_mem := fun value hvalue => hgraphHorizontal (coordinates (value - point)) hvalue
    mem_iff := ?_ }, ?_⟩
  · intro value hvalue
    have h := hgraphSubset (coordinates (value - point)) hvalue
    change homeomorph (coordinates (value - point)) ∈ subset ↔ _ at h
    have heq : homeomorph (coordinates (value - point)) = value := by
      change point + coordinates.symm (coordinates (value - point)) = value
      simp
    simpa only [heq] using h
  · intro parameter hparameter tangent
    change normal (homeomorph (graph parameter, parameter))
      (coordinates.symm (fderiv ℝ graph parameter tangent, tangent)) = 0
    have h := hgraphNormal parameter hparameter tangent
    have hequal := hdecompose (graph parameter, parameter) 0
      (fderiv ℝ graph parameter tangent, tangent)
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, hdifference] at hequal
    exact hequal.symm.trans h

end BoundedUncertainty
