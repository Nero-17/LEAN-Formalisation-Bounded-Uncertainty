import BoundedUncertainty.SmoothLocalExtension
import BoundedUncertainty.SmoothImplicitRadius
import BoundedUncertainty.HigherExponentialInverse

/-!
# A smooth extension of the actual exponential inverse

The scalar solution is smooth on a fixed open neighborhood. Composing it
with one fixed smooth gradient extension gives one fixed smooth extension
of the inverse. Only the actual inverse values on its range are identified.
-/

namespace BoundedUncertainty

open Set Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiffOn_exponentialInverseFormula {order : WithTop ℕ∞}
    (solution : E × E → ℝ) (gradient : E → E) (U : Set (E × E)) (V : Set E)
    (hsolution : ContDiffOn ℝ order solution U) (hgradient : ContDiffOn ℝ order gradient V)
    (hcentre : MapsTo (fun p : E × E => p.1 - solution p • p.2) U V)
    (hnonzero : ∀ p ∈ U, p.2 + gradient (p.1 - solution p • p.2) ≠ 0) :
    ContDiffOn ℝ order (exponentialInverseFormula solution gradient) U := by
  have hcentreSmooth : ContDiffOn ℝ order
      (fun p : E × E => p.1 - solution p • p.2) U :=
    contDiffOn_fst.sub (hsolution.smul contDiffOn_snd)
  have hnormal : ContDiffOn ℝ order
      (fun p : E × E => p.2 + gradient (p.1 - solution p • p.2)) U :=
    contDiffOn_snd.add (hgradient.comp hcentreSmooth hcentre)
  exact hcentreSmooth.prodMk (((hnormal.norm ℝ hnonzero).inv
    (fun p hp => norm_ne_zero_iff.mpr (hnonzero p hp))).smul hnormal)

variable [CompleteSpace E] {r s : ℕ}

/-- The canonical radius gradient inherits one fixed smooth local extension. -/
theorem SetValuedSystem.hasSmoothLocalExtensionOn_radiusGradientOnAmbient
    (system : SetValuedSystem (E := E) r s)
    (hRadius : HasSmoothLocalExtensionOn system.domain system.radius) :
    HasSmoothLocalExtensionOn system.domain system.radiusGradientOnAmbient := by
  apply hRadius.derivative_map system.radius_extension system.regular_closed
    system.radius_order_pos
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  intro y
  exact system.radiusGradientOnAmbient_apply y

/-- A continuous actual exponential inverse is smoothly extendible, using
one fixed C-infinity neighborhood at each output point. -/
theorem SetValuedSystem.hasSmoothLocalExtensionOn_exponentialInverse_of_continuous
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hRadius : HasSmoothLocalExtensionOn system.domain system.radius)
    (inverse : E × E → E × E) (Y : Set (E × E))
    (hcontinuous : ContinuousOn inverse Y)
    (hmaps : MapsTo inverse Y (system.domain ×ˢ {n : E | ‖n‖ = 1}))
    (hright : ∀ p ∈ Y,
      exponentialMap system.radius system.radiusGradientOnAmbient (inverse p) = p) :
    HasSmoothLocalExtensionOn Y inverse := by
  apply hasSmoothLocalExtensionOn_of_locally_contDiffOn
  intro p hp
  obtain ⟨radiusExtension⟩ := hRadius (inverse p).1 (hmaps hp).1
  obtain ⟨gradientExtension⟩ := (system.hasSmoothLocalExtensionOn_radiusGradientOnAmbient hRadius)
    (inverse p).1 (hmaps hp).1
  have hradius : radiusExtension.extension (inverse p).1 = system.radius (inverse p).1 :=
    radiusExtension.agrees ⟨(hmaps hp).1, radiusExtension.mem_neighborhood⟩
  have hgradient : gradientExtension.extension (inverse p).1 =
      system.radiusGradientOnAmbient (inverse p).1 :=
    gradientExtension.agrees ⟨(hmaps hp).1, gradientExtension.mem_neighborhood⟩
  have hnormal : normalUpdate (system.radiusGradientOnAmbient (inverse p).1)
      (inverse p).2 = p.2 := congrArg Prod.snd (hright p hp)
  have hposition : (inverse p).1 + system.radius (inverse p).1 • p.2 = p.1 := by
    simpa only [exponentialMap, hnormal] using congrArg Prod.fst (hright p hp)
  have hunit : ‖p.2‖ = 1 := by
    rw [← hnormal]
    exact norm_normalUpdate _ _
      (hcontraction.norm_radiusGradientOnAmbient _ (hmaps hp).1) (hmaps hp).2
  obtain ⟨solution, V, hVopen, hpV, hsolution, hsolutionValue, _, hunique⟩ :=
    exists_smooth_radiusImplicitSolution radiusExtension.extension radiusExtension.neighborhood
      radiusExtension.isOpen_neighborhood radiusExtension.contDiffOn_extension
      (inverse p).1 p.2 radiusExtension.mem_neighborhood
      ((InnerProductSpace.toDual ℝ E) (system.radiusGradientOnAmbient (inverse p).1))
      (system.hasFDerivAt_radiusExtension ⟨(inverse p).1, (hmaps hp).1⟩
        (radiusExtension.toLocalExtensionAt r))
      (radiusImplicitEquation_partial_pos _ _
        (hcontraction.norm_radiusGradientOnAmbient _ (hmaps hp).1) hunit).ne'
  rw [hradius, hposition, Prod.eta] at hpV hsolutionValue hunique
  have hcentreValue : p.1 - solution p • p.2 = (inverse p).1 := by
    rw [hsolutionValue, ← hposition, add_sub_cancel_right]
  have hcentreContinuous : ContinuousAt
      (fun q : E × E => q.1 - solution q • q.2) p :=
    continuousAt_fst.sub
      ((hsolution.continuousOn.continuousAt (hVopen.mem_nhds hpV)).smul continuousAt_snd)
  have hgradientNeighborhood : ∀ᶠ q in 𝓝 p,
      q.1 - solution q • q.2 ∈ gradientExtension.neighborhood :=
    hcentreContinuous (by
      change gradientExtension.neighborhood ∈ 𝓝 (p.1 - solution p • p.2)
      rw [hcentreValue]
      exact gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood)
  have hnormalContinuous : ContinuousAt (fun q : E × E =>
      q.2 + gradientExtension.extension (q.1 - solution q • q.2)) p := by
    apply continuousAt_snd.add
    have hgradientContinuous := gradientExtension.contDiffOn_extension.continuousOn.continuousAt
      (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood)
    exact hgradientContinuous.comp_of_eq hcentreContinuous hcentreValue
  have hnormalNonzero : ∀ᶠ q in 𝓝 p,
      q.2 + gradientExtension.extension (q.1 - solution q • q.2) ≠ 0 :=
    hnormalContinuous (isOpen_compl_singleton.mem_nhds (by
      change p.2 + gradientExtension.extension (p.1 - solution p • p.2) ≠ 0
      rw [hcentreValue, hgradient]
      exact unit_add_gradient_ne_zero _ _
        (hcontraction.norm_radiusGradientOnAmbient _ (hmaps hp).1) hunit))
  obtain ⟨W, hWsubset, hWopen, hpW⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem (hVopen.mem_nhds hpV) hgradientNeighborhood) hnormalNonzero)
  refine ⟨exponentialInverseFormula solution gradientExtension.extension, W, hWopen, hpW,
    contDiffOn_exponentialInverseFormula _ _ W gradientExtension.neighborhood
      (hsolution.mono (fun q hq => (hWsubset hq).1.1)) gradientExtension.contDiffOn_extension
      (fun q hq => (hWsubset hq).1.2) (fun q hq => (hWsubset hq).2), ?_⟩
  apply eventually_nhdsWithin_iff.mp
  have hcentreInverseContinuous : ContinuousWithinAt (fun q => (inverse q).1) Y p :=
    (hcontinuous p hp).fst
  have hradiusInverseContinuous : ContinuousWithinAt
      (fun q => system.radius (inverse q).1) Y p :=
    (system.radius_extension.continuousOn (inverse p).1 (hmaps hp).1).comp
      (f := fun q => (inverse q).1) hcentreInverseContinuous (fun q hq => (hmaps hq).1)
  have hscalarContinuous : Tendsto
      (fun q : E × E => (q, system.radius (inverse q).1)) (𝓝[Y] p)
      (𝓝 (p, system.radius (inverse p).1)) :=
    continuousWithinAt_id.prodMk hradiusInverseContinuous
  have hradiusNeighborhood := hcentreInverseContinuous
    (radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood)
  have hgradientInverseNeighborhood := hcentreInverseContinuous
    (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood)
  filter_upwards [self_mem_nhdsWithin, hscalarContinuous hunique,
    hradiusNeighborhood, hgradientInverseNeighborhood] with q hq hqUnique hqRadius hqGradient
  have hqNormal : normalUpdate (system.radiusGradientOnAmbient (inverse q).1)
      (inverse q).2 = q.2 := congrArg Prod.snd (hright q hq)
  have hqPosition : (inverse q).1 + system.radius (inverse q).1 • q.2 = q.1 := by
    simpa only [exponentialMap, hqNormal] using congrArg Prod.fst (hright q hq)
  have hqCentre : q.1 - system.radius (inverse q).1 • q.2 = (inverse q).1 := by
    rw [← hqPosition, add_sub_cancel_right]
  have hqSolution : solution q = system.radius (inverse q).1 := by
    apply hqUnique
    simp only [radiusImplicitEquation, hqCentre,
      radiusExtension.agrees ⟨(hmaps hq).1, hqRadius⟩, sub_self]
  apply Prod.ext
  · change q.1 - solution q • q.2 = (inverse q).1
    rw [hqSolution]
    exact hqCentre
  · change ‖q.2 + gradientExtension.extension (q.1 - solution q • q.2)‖⁻¹ •
      (q.2 + gradientExtension.extension (q.1 - solution q • q.2)) = (inverse q).2
    rw [hqSolution, hqCentre, gradientExtension.agrees ⟨(hmaps hq).1, hqGradient⟩, ← hqNormal]
    exact normalize_normalUpdate_add_gradient _ _
      (hcontraction.norm_radiusGradientOnAmbient _ (hmaps hq).1) (hmaps hq).2

end BoundedUncertainty
