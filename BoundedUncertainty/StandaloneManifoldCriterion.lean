import BoundedUncertainty.ArbitrarySequentialGraph
import BoundedUncertainty.InvarianceOfDomain
import BoundedUncertainty.FrontierGraphReparametrization
import BoundedUncertainty.ChartedSpaceModelTransport

/-!
The standalone codimension-one manifold criterion. The analytic graph theorem
is applied only after projection openness has been proved from invariance of
domain on the actual topological manifold. The normal field is defined only on
the subset in the final interface, and the original moving endpoints remain
distinct. No C1 structure, regular-closed domain, or frontier is assumed.
-/

namespace BoundedUncertainty

open Set Topology Filter

/-- The intersection subtype and its corresponding relative open subset
carry exactly the same topology. -/
def intersectionSubtypeHomeomorph {X : Type*} [TopologicalSpace X] (subset patch : Set X) :
    ↥(subset ∩ patch) ≃ₜ ↥((Subtype.val : subset → X) ⁻¹' patch) where
  toFun point := ⟨⟨point, point.property.1⟩, point.property.2⟩
  invFun point := ⟨point, point.val.property, point.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk (fun point => point.property.1)).subtype_mk
      (fun point => point.property.2)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun point => ⟨point.val.property, point.property⟩)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Invariance of domain discharges the open-projection premise for a genuine
topological manifold of the required dimension. -/
theorem exists_c1HypersurfaceGraphAt_of_manifold_distinct_secants
    (subset : Set E) [ChartedSpace (Fin (Module.finrank ℝ E - 1) → ℝ) subset]
    (normal : E → E) (hcontinuous : ContinuousOn normal subset)
    (hunit : ∀ point ∈ subset, ‖normal point‖ = 1)
    (hsecants : ∀ point ∈ subset, ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |inner ℝ (normal point) (second index - first index)| /
        ‖second index - first index‖) atTop (𝓝 0))
    (point : E) (hpoint : point ∈ subset) :
    ∃ chart : C1HypersurfaceGraphAt (F := (innerSL ℝ (normal point)).ker) subset point,
      ∀ horizontal ∈ chart.graphDomain, ∀ tangent : (innerSL ℝ (normal point)).ker,
        inner ℝ (normal (point + chart.coordinates.symm (chart.graph horizontal, horizontal)))
          (chart.coordinates.symm (fderiv ℝ chart.graph horizontal tangent, tangent)) = 0 := by
  have hnonzero : innerSL ℝ (normal point) ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm hzero
    simp only [innerSL_apply_norm, hunit point hpoint, norm_zero] at hnorm
    exact one_ne_zero hnorm
  letI : ChartedSpace (innerSL ℝ (normal point)).ker subset :=
    chartedSpaceChangeModel (normalKernelEquiv (innerSL ℝ (normal point)) hnonzero).symm.toHomeomorph
  obtain ⟨radius, hradius, hinjective⟩ :=
    exists_injOn_unitNormalProjection_of_distinct_secants subset point (normal point)
      (hunit point hpoint) (hsecants point hpoint)
  have hprojection := isOpenMap_restrict_of_continuous_injOn
    (fun value : subset =>
      (unitNormalCoordinates (normal point) (hunit point hpoint) ((value : E) - point)).2)
    (Subtype.val ⁻¹' Metric.ball point radius)
    (Metric.isOpen_ball.preimage continuous_subtype_val)
    ((unitNormalCoordinates (normal point) (hunit point hpoint)).continuous.comp
      (continuous_subtype_val.sub continuous_const)).snd
    (by
      intro first hfirst second hsecond hequal
      apply Subtype.ext
      exact hinjective ⟨first.property, hfirst⟩ ⟨second.property, hsecond⟩ hequal)
  have hprojectionIntersection : IsOpenMap
      (fun value : ↥(subset ∩ Metric.ball point radius) =>
        (unitNormalCoordinates (normal point) (hunit point hpoint) ((value : E) - point)).2) :=
    hprojection.comp (intersectionSubtypeHomeomorph subset (Metric.ball point radius)).isOpenMap
  exact exists_c1HypersurfaceGraphAt_of_distinct_normal_secants_and_open_projection
    subset normal hcontinuous hunit hsecants point hpoint (Metric.ball point radius)
    Metric.isOpen_ball (Metric.mem_ball_self hradius) hprojectionIntersection

/-- An ambient representative used only to apply the analytic interface. -/
noncomputable def subsetNormalExtension (subset : Set E) (normal : subset → E) : E → E := by
  classical
  exact fun point => if hpoint : point ∈ subset then normal ⟨point, hpoint⟩ else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem subsetNormalExtension_apply (subset : Set E) (normal : subset → E)
    (point : subset) : subsetNormalExtension subset normal point = normal point := by
  simp only [subsetNormalExtension, dif_pos point.property]

/-- The original standalone 4.8 interface: a continuous unit normal field on
the actual topological manifold and distinct moving secants give genuine C1
graphs with that field normal to every graph tangent. -/
theorem exists_c1HypersurfaceGraphAt_of_continuous_unit_normal
    (subset : Set E) [ChartedSpace (Fin (Module.finrank ℝ E - 1) → ℝ) subset]
    (normal : subset → E) (hcontinuous : Continuous normal)
    (hunit : ∀ point, ‖normal point‖ = 1)
    (hsecants : ∀ point : subset, ∀ first second : ℕ → subset,
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |inner ℝ (normal point)
        ((second index : E) - (first index : E))| /
          ‖(second index : E) - (first index : E)‖) atTop (𝓝 0))
    (point : subset) :
    ∃ chart : C1HypersurfaceGraphAt (F := (innerSL ℝ (normal point)).ker) subset point,
      ∀ (horizontal : (innerSL ℝ (normal point)).ker) (hhorizontal : horizontal ∈ chart.graphDomain),
        ∀ tangent : (innerSL ℝ (normal point)).ker,
        inner ℝ (normal ⟨point + chart.coordinates.symm (chart.graph horizontal, horizontal),
          chart.graph_mem horizontal hhorizontal⟩)
          (chart.coordinates.symm (fderiv ℝ chart.graph horizontal tangent, tangent)) = 0 := by
  have hnormalContinuous : ContinuousOn (subsetNormalExtension subset normal) subset := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun value : subset => subsetNormalExtension subset normal value)
    exact hcontinuous.congr (fun value => (subsetNormalExtension_apply subset normal value).symm)
  have hnormalUnit : ∀ value ∈ subset, ‖subsetNormalExtension subset normal value‖ = 1 := by
    intro value hvalue
    simpa only [subsetNormalExtension, dif_pos hvalue] using hunit ⟨value, hvalue⟩
  have hnormalSecants : ∀ value ∈ subset, ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 value) → Tendsto second atTop (𝓝 value) →
      Tendsto (fun index => |inner ℝ (subsetNormalExtension subset normal value)
        (second index - first index)| / ‖second index - first index‖) atTop (𝓝 0) := by
    intro value hvalue first second hfirstMem hsecondMem hdistinct hfirst hsecond
    have h := hsecants ⟨value, hvalue⟩
      (fun index => ⟨first index, hfirstMem index⟩)
      (fun index => ⟨second index, hsecondMem index⟩)
      (fun index hequal => hdistinct index (congrArg Subtype.val hequal))
      (tendsto_subtype_rng.mpr hfirst) (tendsto_subtype_rng.mpr hsecond)
    simpa only [subsetNormalExtension, dif_pos hvalue] using h
  have h := exists_c1HypersurfaceGraphAt_of_manifold_distinct_secants subset
    (subsetNormalExtension subset normal) hnormalContinuous hnormalUnit hnormalSecants
    point point.property
  rw [subsetNormalExtension_apply subset normal point] at h
  obtain ⟨chart, hchartNormal⟩ := h
  refine ⟨chart, ?_⟩
  intro horizontal hhorizontal tangent
  have h := hchartNormal horizontal hhorizontal tangent
  simpa only [subsetNormalExtension, dif_pos (chart.graph_mem horizontal hhorizontal)] using h

end BoundedUncertainty
