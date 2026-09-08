import BoundedUncertainty.ArbitraryGraphProjection

/-! Local quantitative and analytic steps for an arbitrary subset. The local
open-map assumption is explicit and is not inferred from the secant bounds.
`StandaloneManifoldCriterion` supplies it using invariance of domain. -/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem exists_cone_ball_of_littleO_vertical_chord {subset : Set (ℝ × F)}
    (hsecant : (fun pair : (ℝ × F) × (ℝ × F) => pair.2.1 - pair.1.1)
      =o[𝓝[subset ×ˢ subset] (0, 0)] (fun pair => pair.2 - pair.1)) :
    ∃ radius > 0, ∀ first ∈ subset ∩ Metric.ball 0 radius,
      ∀ second ∈ subset ∩ Metric.ball 0 radius,
      |first.1 - second.1| ≤ ‖first.2 - second.2‖ := by
  obtain ⟨radius, hradius, hbound⟩ := Metric.mem_nhdsWithin_iff.mp
    (hsecant.def (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨radius, hradius, ?_⟩
  intro first hfirst second hsecond
  have hpair : (first, second) ∈ Metric.ball ((0 : ℝ × F), 0) radius := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using
      And.intro hfirst.2 hsecond.2
  have hsmall := hbound ⟨hpair, ⟨hfirst.1, hsecond.1⟩⟩
  change ‖second.1 - first.1‖ ≤ 1 / 2 * ‖second - first‖ at hsmall
  rw [Prod.norm_def, Real.norm_eq_abs] at hsmall
  simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs] at hsmall
  rw [abs_sub_comm, norm_sub_rev] at hsmall
  by_cases hle : |first.1 - second.1| ≤ ‖first.2 - second.2‖
  · exact hle
  · rw [max_eq_left (le_of_not_ge hle)] at hsmall
    nlinarith [abs_nonneg (first.1 - second.1), norm_nonneg (first.2 - second.2)]

omit [NormedSpace ℝ F] in
theorem isOpen_projection_image_of_restricted_openMap
    {subset patch neighborhood : Set (ℝ × F)}
    (hprojection : IsOpenMap (fun point : ↥(subset ∩ patch) => (point : ℝ × F).2))
    (hneighborhood : IsOpen neighborhood) (hsubset : neighborhood ⊆ patch) :
    IsOpen (Prod.snd '' (subset ∩ neighborhood)) := by
  have hopen := hprojection (Subtype.val ⁻¹' neighborhood)
    (hneighborhood.preimage continuous_subtype_val)
  convert hopen using 1
  ext horizontal
  constructor
  · rintro ⟨point, hpoint, rfl⟩
    exact ⟨⟨point, hpoint.1, hsubset hpoint.2⟩, hpoint.2, rfl⟩
  · rintro ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨point.property.1, hpoint⟩, rfl⟩

/-- All analytic conclusions are obtained on an actual ambient neighbourhood.
The local projection map being open is the sole additional topological premise. -/
theorem exists_c1_graph_of_local_normal_chords_and_open_projection
    {subset patch : Set (ℝ × F)} (hzero : (0 : ℝ × F) ∈ subset)
    (hpatch : IsOpen patch) (hzeroPatch : (0 : ℝ × F) ∈ patch)
    (hprojection : IsOpenMap (fun point : ↥(subset ∩ patch) => (point : ℝ × F).2))
    (hflat : (fun pair : (ℝ × F) × (ℝ × F) => pair.2.1 - pair.1.1)
      =o[𝓝[subset ×ˢ subset] (0, 0)] (fun pair => pair.2 - pair.1))
    (horizontal : (ℝ × F) → F →L[ℝ] ℝ) (vertical : (ℝ × F) → ℝ)
    (hhorizontal : ContinuousOn horizontal subset)
    (hvertical : ContinuousOn vertical subset) (hnonzero : vertical 0 ≠ 0)
    (hsecant : ∀ point ∈ subset,
      (fun other => vertical point * (other.1 - point.1) + horizontal point (other.2 - point.2))
        =o[𝓝[subset] point] (fun other => other - point)) :
    ∃ neighborhood : Set (ℝ × F), IsOpen neighborhood ∧ 0 ∈ neighborhood ∧
      ∃ domain : Set F, IsOpen domain ∧ 0 ∈ domain ∧
        ∃ graph : F → ℝ, graph 0 = 0 ∧ ContDiffOn ℝ 1 graph domain ∧
          (∀ point ∈ domain, (graph point, point) ∈ subset) ∧
          (∀ other ∈ neighborhood, other ∈ subset ↔ other.1 = graph other.2) ∧
          (∀ other ∈ neighborhood, other.2 ∈ domain) ∧
          (∀ point ∈ domain, ∀ tangent : F,
            vertical (graph point, point) * (fderiv ℝ graph point tangent) +
              horizontal (graph point, point) tangent = 0) := by
  obtain ⟨radius, hradius, hcone⟩ := exists_cone_ball_of_littleO_vertical_chord hflat
  have htransverse : ∀ᶠ point in 𝓝[subset] (0 : ℝ × F), vertical point ≠ 0 :=
    (hvertical 0 hzero).eventually (isOpen_compl_singleton.mem_nhds hnonzero)
  obtain ⟨size, hsize, hsizeNonzero⟩ := Metric.mem_nhdsWithin_iff.mp htransverse
  let neighborhood := patch ∩ Metric.ball (0 : ℝ × F) radius ∩ Metric.ball 0 size
  have hopen : IsOpen neighborhood := (hpatch.inter Metric.isOpen_ball).inter Metric.isOpen_ball
  have hzeroNeighborhood : (0 : ℝ × F) ∈ neighborhood :=
    ⟨⟨hzeroPatch, Metric.mem_ball_self hradius⟩, Metric.mem_ball_self hsize⟩
  have hprojectionOpen : IsOpen (Prod.snd '' (subset ∩ neighborhood)) :=
    isOpen_projection_image_of_restricted_openMap hprojection hopen (fun _ h => h.1.1)
  have hverticalNonzero (point : ℝ × F) (hpoint : point ∈ subset ∩ neighborhood) :
      vertical point ≠ 0 := hsizeNonzero ⟨hpoint.2.2, hpoint.1⟩
  obtain ⟨graph, hgraphZero, hgraphSmooth, hgraphMember, hgraphSubset, hgraphDerivative⟩ :=
    exists_c1_graph_of_cone_and_open_projection ⟨hzero, hzeroNeighborhood⟩ hprojectionOpen 1
      (fun first hfirst second hsecond => by
        simpa only [NNReal.coe_one, one_mul] using
          hcone first ⟨hfirst.1, hfirst.2.1.2⟩ second ⟨hsecond.1, hsecond.2.1.2⟩)
      horizontal vertical (hhorizontal.mono inter_subset_left)
      (hvertical.mono inter_subset_left) hverticalNonzero
      (fun point hpoint => hsecant point hpoint.1)
  have hzeroImage : (0 : F) ∈ Prod.snd '' (subset ∩ neighborhood) :=
    ⟨0, ⟨hzero, hzeroNeighborhood⟩, rfl⟩
  refine ⟨neighborhood ∩ Prod.snd ⁻¹' (Prod.snd '' (subset ∩ neighborhood)),
    hopen.inter (hprojectionOpen.preimage continuous_snd), ⟨hzeroNeighborhood, hzeroImage⟩,
    Prod.snd '' (subset ∩ neighborhood), hprojectionOpen, hzeroImage, graph,
    hgraphZero, hgraphSmooth, fun point hpoint => (hgraphMember point hpoint).1,
    fun other hother => hgraphSubset other hother.1 hother.2,
    fun _ hother => hother.2, ?_⟩
  intro point hpoint tangent
  rw [(hgraphDerivative point hpoint).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hnonzeroPoint := hverticalNonzero _ (hgraphMember point hpoint)
  field_simp
  ring

end BoundedUncertainty
