import BoundedUncertainty.ArbitraryNormalGraph

/-! The original distinct-endpoint secant hypothesis supplies all analytic
premises of the arbitrary-subset criterion. Local projection openness remains
explicit here. `StandaloneManifoldCriterion` discharges it from the original
topological manifold hypothesis and proves the unconditional conclusion. -/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Coordinates in the actual orthogonal kernel of a supplied unit normal. -/
noncomputable def unitNormalCoordinates (normal : E) (hunit : ‖normal‖ = 1) :
    E ≃L[ℝ] ℝ × (innerSL ℝ normal).ker :=
  normalCoordinates (innerSL ℝ normal) normal (by
    simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq, hunit, one_pow])

@[simp] theorem unitNormalCoordinates_snd_coe (normal : E) (hunit : ‖normal‖ = 1)
    (point : E) : ((unitNormalCoordinates normal hunit point).2 : E) =
      point - inner ℝ normal point • normal := rfl

/-- The actual projection used in the conditional graph theorem is locally
injective under the distinct-endpoint hypothesis alone. -/
theorem exists_injOn_unitNormalProjection_of_distinct_secants
    (subset : Set E) (point normal : E) (hunit : ‖normal‖ = 1)
    (hsequences : ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |inner ℝ normal (second index - first index)| /
        ‖second index - first index‖) atTop (𝓝 0)) :
    ∃ radius > 0, InjOn (fun value : E =>
      (unitNormalCoordinates normal hunit (value - point)).2)
      (subset ∩ Metric.ball point radius) := by
  obtain ⟨radius, hradius, hinjective⟩ :=
    exists_injOn_orthogonalProjection_of_distinct_secants subset point normal hunit hsequences
  refine ⟨radius, hradius, ?_⟩
  intro first hfirst second hsecond hequal
  apply hinjective hfirst hsecond
  have hcast := congrArg (fun value : (innerSL ℝ normal).ker => (value : E)) hequal
  simp only [unitNormalCoordinates_snd_coe] at hcast
  have htranslate :
      (first - inner ℝ normal first • normal) - (point - inner ℝ normal point • normal) =
      (second - inner ℝ normal second • normal) - (point - inner ℝ normal point • normal) := by
    convert hcast using 1 <;> simp only [inner_sub_right, sub_smul] <;> abel
  exact sub_left_inj.mp htranslate

/-- Conditional form of the standalone 4.8 conclusion, with the exact
distinct-endpoint sequences and continuous unit normals on the actual subset. -/
theorem exists_c1HypersurfaceGraphAt_of_distinct_normal_secants_and_open_projection
    (subset : Set E) (normal : E → E) (hcontinuous : ContinuousOn normal subset)
    (hunit : ∀ point ∈ subset, ‖normal point‖ = 1)
    (hsecants : ∀ point ∈ subset, ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |inner ℝ (normal point) (second index - first index)| /
        ‖second index - first index‖) atTop (𝓝 0))
    (point : E) (hpoint : point ∈ subset)
    (patch : Set E) (hpatch : IsOpen patch) (hpointPatch : point ∈ patch)
    (hprojection : IsOpenMap (fun value : ↥(subset ∩ patch) =>
      (unitNormalCoordinates (normal point) (hunit point hpoint) ((value : E) - point)).2)) :
    ∃ chart : C1HypersurfaceGraphAt (F := (innerSL ℝ (normal point)).ker) subset point,
      ∀ horizontal ∈ chart.graphDomain, ∀ tangent : (innerSL ℝ (normal point)).ker,
        inner ℝ (normal (point + chart.coordinates.symm (chart.graph horizontal, horizontal)))
          (chart.coordinates.symm (fderiv ℝ chart.graph horizontal tangent, tangent)) = 0 := by
  have hcovector : ContinuousOn (fun value => innerSL ℝ (normal value)) subset :=
    (innerSL ℝ).continuous.comp_continuousOn hcontinuous
  have hlittleO : ∀ value ∈ subset,
      (fun pair : E × E => innerSL ℝ (normal value) (pair.2 - pair.1))
        =o[𝓝[subset ×ˢ subset] (value, value)] (fun pair => pair.2 - pair.1) := by
    intro value hvalue
    exact isLittleO_chord_of_distinct_normalized_secants subset value
      (innerSL ℝ (normal value)) (hsecants value hvalue)
  have htransverse : innerSL ℝ (normal point) (normal point) = 1 := by
    simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq, hunit point hpoint, one_pow]
  exact exists_c1HypersurfaceGraphAt_of_normal_chords_and_open_projection
    subset (fun value => innerSL ℝ (normal value)) hcovector hlittleO point hpoint
    (normal point) htransverse patch hpatch hpointPatch hprojection

end BoundedUncertainty
