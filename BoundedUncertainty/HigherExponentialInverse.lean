import BoundedUncertainty.ImplicitRadius
import BoundedUncertainty.LocalExtensionOperations

/-!
# Local ambient regularity of a continuous exponential inverse

The scalar implicit solution recovers the radius, then the centre and the
normal.  This applies to a continuous inverse on any actual image subset; no
closedness or smooth-boundary hypothesis is imposed on that subset.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- The inverse expression once the scalar implicit radius has been solved. -/
noncomputable def exponentialInverseFormula (solution : E × E → ℝ) (gradient : E → E)
    (p : E × E) : E × E :=
  (p.1 - solution p • p.2,
    ‖p.2 + gradient (p.1 - solution p • p.2)‖⁻¹ •
      (p.2 + gradient (p.1 - solution p • p.2)))

omit [CompleteSpace E] in
/-- The centre and inverse normal are smooth wherever the shifted normal is nonzero. -/
theorem contDiffAt_exponentialInverseFormula {order : WithTop ℕ∞}
    (solution : E × E → ℝ) (gradient : E → E) (p : E × E)
    (hsolution : ContDiffAt ℝ order solution p)
    (hgradient : ContDiffAt ℝ order gradient (p.1 - solution p • p.2))
    (hnonzero : p.2 + gradient (p.1 - solution p • p.2) ≠ 0) :
    ContDiffAt ℝ order (exponentialInverseFormula solution gradient) p := by
  have hcentre : ContDiffAt ℝ order (fun q : E × E => q.1 - solution q • q.2) p :=
    contDiffAt_fst.sub (hsolution.smul contDiffAt_snd)
  have hnormal : ContDiffAt ℝ order
      (fun q : E × E => q.2 + gradient (q.1 - solution q • q.2)) p :=
    contDiffAt_snd.add (hgradient.comp p hcentre)
  exact hcentre.prodMk (((hnormal.norm ℝ hnonzero).inv
    (norm_ne_zero_iff.mpr hnonzero)).smul hnormal)

/-- Every local radius extension has the actual canonical gradient as its differential. -/
theorem SetValuedSystem.hasFDerivAt_radiusExtension
    (system : SetValuedSystem (E := E) r s) (y : system.domain)
    (extension : LocalExtensionAt r system.domain system.radius y) :
    HasFDerivAt extension.extension
      ((InnerProductSpace.toDual ℝ E) (system.radiusGradientOnAmbient y)) y := by
  have hdifferentiable :=
    (extension.contDiffOn_extension.contDiffAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)).differentiableAt
        (by exact_mod_cast (Nat.ne_of_gt system.radius_order_pos))
  convert hdifferentiable.hasFDerivAt using 1
  rw [system.radiusGradientOnAmbient_apply]
  change (InnerProductSpace.toDual ℝ E)
    ((InnerProductSpace.toDual ℝ E).symm (system.radius_extension.ambientDerivative y)) = _
  rw [(InnerProductSpace.toDual ℝ E).apply_symm_apply]
  exact system.radius_extension.ambientDerivative_eq_extension system.regular_closed
    system.radius_order_pos system.radius_order_pos extension y extension.mem_neighborhood

/-- Any continuous right inverse of the genuine exponential formula, with
preimages in the domain unit bundle, has local `C^(r-1)` ambient extensions.
Continuity here is the topological inverse property already supplied by the
exponential embedding; it is not a differentiability hypothesis. -/
theorem SetValuedSystem.hasLocalExtensionOn_exponentialInverse_of_continuous
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (inverse : E × E → E × E) (Y : Set (E × E))
    (hcontinuous : ContinuousOn inverse Y)
    (hmaps : MapsTo inverse Y (system.domain ×ˢ {n : E | ‖n‖ = 1}))
    (hright : ∀ p ∈ Y,
      exponentialMap system.radius system.radiusGradientOnAmbient (inverse p) = p) :
    HasLocalExtensionOn (r - 1) Y inverse := by
  apply hasLocalExtensionOn_of_locally_contDiffAt
  intro p hp
  obtain ⟨radiusExtension⟩ := system.radius_extension (inverse p).1 (hmaps hp).1
  obtain ⟨gradientExtension⟩ := system.hasLocalExtensionOn_radiusGradientOnAmbient
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
  have hradiusSmooth : ContDiffAt ℝ r radiusExtension.extension (inverse p).1 :=
    radiusExtension.contDiffOn_extension.contDiffAt
      (radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood)
  obtain ⟨solution, hsolution, hsolutionValue, _, hunique⟩ :=
    exists_contDiffAt_radiusImplicitSolution radiusExtension.extension (inverse p).1 p.2
      ((InnerProductSpace.toDual ℝ E) (system.radiusGradientOnAmbient (inverse p).1))
      system.radius_order_pos hradiusSmooth
      (system.hasFDerivAt_radiusExtension ⟨(inverse p).1, (hmaps hp).1⟩ radiusExtension)
      (radiusImplicitEquation_partial_pos _ _
        (hcontraction.norm_radiusGradientOnAmbient _ (hmaps hp).1) hunit).ne'
  rw [hradius, hposition, Prod.eta] at hsolution hsolutionValue hunique
  have hcentreValue : p.1 - solution p • p.2 = (inverse p).1 := by
    rw [hsolutionValue, ← hposition, add_sub_cancel_right]
  have hgradientSmooth : ContDiffAt ℝ (r - 1 : ℕ)
      gradientExtension.extension (p.1 - solution p • p.2) := by
    rw [hcentreValue]
    exact gradientExtension.contDiffOn_extension.contDiffAt
      (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood)
  refine ⟨exponentialInverseFormula solution gradientExtension.extension,
    contDiffAt_exponentialInverseFormula _ _ p
      (hsolution.of_le (by exact_mod_cast (Nat.sub_le r 1))) hgradientSmooth ?_, ?_⟩
  · rw [hcentreValue, hgradient]
    exact unit_add_gradient_ne_zero _ _
      (hcontraction.norm_radiusGradientOnAmbient _ (hmaps hp).1) hunit
  · apply eventually_nhdsWithin_iff.mp
    have hcentreContinuous : ContinuousWithinAt (fun q => (inverse q).1) Y p :=
      (hcontinuous p hp).fst
    have hradiusContinuous : ContinuousWithinAt
        (fun q => system.radius (inverse q).1) Y p :=
      (system.radius_extension.continuousOn (inverse p).1 (hmaps hp).1).comp
        (f := fun q => (inverse q).1) hcentreContinuous (fun q hq => (hmaps hq).1)
    have hscalarContinuous : Tendsto
        (fun q : E × E => (q, system.radius (inverse q).1)) (𝓝[Y] p)
        (𝓝 (p, system.radius (inverse p).1)) :=
      continuousWithinAt_id.prodMk hradiusContinuous
    have hradiusNeighborhood := hcentreContinuous
      (radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood)
    have hgradientNeighborhood := hcentreContinuous
      (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood)
    filter_upwards [self_mem_nhdsWithin, hscalarContinuous hunique,
      hradiusNeighborhood, hgradientNeighborhood] with q hq hqUnique hqRadius hqGradient
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
      rw [hqSolution, hqCentre, gradientExtension.agrees ⟨(hmaps hq).1, hqGradient⟩,
        ← hqNormal]
      exact normalize_normalUpdate_add_gradient _ _
        (hcontraction.norm_radiusGradientOnAmbient _ (hmaps hq).1) (hmaps hq).2

end BoundedUncertainty
