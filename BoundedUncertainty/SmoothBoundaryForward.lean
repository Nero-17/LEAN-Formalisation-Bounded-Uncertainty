import BoundedUncertainty.SmoothLocalExtension
import BoundedUncertainty.HigherBoundaryMap
import BoundedUncertainty.HigherLinearInverse

/-! Smooth forward and linear inverse formulas on fixed local neighborhoods. -/
namespace BoundedUncertainty
open Set Filter Topology
open scoped ContDiff

section NormedSpaces

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A single representative smooth at every point of a neighborhood gives a fixed smooth witness. -/
theorem hasSmoothLocalExtensionOn_of_eventually_contDiffAt {X : Set E} {f : E → F}
    (h : ∀ x ∈ X, ∃ extension : E → F, ∀ᶠ y in 𝓝 x,
      ContDiffAt ℝ ∞ extension y ∧ (y ∈ X → extension y = f y)) :
    HasSmoothLocalExtensionOn X f := by
  intro x hx
  obtain ⟨extension, heventually⟩ := h x hx
  obtain ⟨U, hUsubset, hUopen, hxU⟩ := mem_nhds_iff.mp heventually
  exact ⟨{
    neighborhood := U
    isOpen_neighborhood := hUopen
    mem_neighborhood := hxU
    extension := extension
    contDiffOn_extension := fun y hy => (hUsubset hy).1.contDiffWithinAt
    agrees := fun y hy => (hUsubset hy.2).2 hy.1
  }⟩

theorem hasSmoothLocalExtensionOn_of_contDiff (X : Set E) (f : E → F)
    (h : ContDiff ℝ ∞ f) : HasSmoothLocalExtensionOn X f := by
  apply hasSmoothLocalExtensionOn_of_eventually_contDiffAt
  intro x _
  exact ⟨f, Filter.Eventually.of_forall (fun y => ⟨h.contDiffAt, fun _ => rfl⟩)⟩

end NormedSpaces

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- This version works throughout an ambient neighborhood, whose normals need not be unit. -/
theorem contDiffAt_linearLiftFormula_of_isUnit {order : WithTop ℕ∞}
    (f : E → E) (D : E → E →L[ℝ] E) (p : E × E)
    (hf : ContDiffAt ℝ order f p.1) (hD : ContDiffAt ℝ order D p.1)
    (hunit : IsUnit (D p.1))
    (hne : ContinuousLinearMap.adjoint (Ring.inverse (D p.1)) p.2 ≠ 0) :
    ContDiffAt ℝ order (linearLiftFormula f D) p := by
  have hinverse : ContDiffAt ℝ order
      (fun operator : E →L[ℝ] E => Ring.inverse operator) (D p.1) := by
    simpa only [hunit.unit_spec] using (contDiffAt_ringInverse ℝ hunit.unit :
      ContDiffAt ℝ order Ring.inverse (hunit.unit : E →L[ℝ] E))
  have hderivativeOnProduct : ContDiffAt ℝ order (fun q : E × E => D q.1) p :=
    hD.comp p contDiffAt_fst
  have hinverseOnProduct : ContDiffAt ℝ order
      (fun q : E × E => Ring.inverse (D q.1)) p :=
    ContDiffAt.comp p
      (g := fun operator : E →L[ℝ] E => Ring.inverse operator)
      (f := fun q : E × E => D q.1) hinverse hderivativeOnProduct
  have hadjoint : ContDiff ℝ order
      (fun operator : E →L[ℝ] E => ContinuousLinearMap.adjoint operator) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).contDiff
  have hoperator : ContDiffAt ℝ order
      (fun q : E × E => ContinuousLinearMap.adjoint (Ring.inverse (D q.1))) p :=
    hadjoint.contDiffAt.comp p hinverseOnProduct
  have hvector : ContDiffAt ℝ order
      (fun q : E × E => ContinuousLinearMap.adjoint (Ring.inverse (D q.1)) q.2) p :=
    hoperator.clm_apply contDiffAt_snd
  exact (hf.comp p contDiffAt_fst).prodMk
    (((hvector.norm ℝ hne).inv (norm_ne_zero_iff.mpr hne)).smul hvector)

omit [CompleteSpace E] in
theorem hasSmoothLocalExtensionOn_exponentialMap {X : Set E}
    (radius : E → ℝ) (gradient : E → E)
    (hradius : HasSmoothLocalExtensionOn X radius)
    (hgradient : HasSmoothLocalExtensionOn X gradient)
    (hbound : ∀ y ∈ X, ‖gradient y‖ < 1) :
    HasSmoothLocalExtensionOn (X ×ˢ (univ : Set E)) (exponentialMap radius gradient) := by
  apply hasSmoothLocalExtensionOn_of_eventually_contDiffAt
  intro p hp
  obtain ⟨radiusExtension⟩ := hradius p.1 hp.1
  obtain ⟨gradientExtension⟩ := hgradient p.1 hp.1
  have hgradientAt := gradientExtension.contDiffOn_extension.contDiffAt
    (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood)
  have hsmall : ‖gradientExtension.extension p.1‖ < 1 := by
    rw [gradientExtension.agrees ⟨hp.1, gradientExtension.mem_neighborhood⟩]
    exact hbound p.1 hp.1
  refine ⟨exponentialMap radiusExtension.extension gradientExtension.extension, ?_⟩
  filter_upwards
    [continuous_fst.continuousAt.preimage_mem_nhds
      (radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood),
     continuous_fst.continuousAt.preimage_mem_nhds
      (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood),
     (hgradientAt.continuousAt.comp continuous_fst.continuousAt).norm.eventually_lt
      continuousAt_const hsmall] with q hqRadius hqGradient hqSmall
  refine ⟨contDiffAt_exponentialMap _ _ q.1 q.2
    (radiusExtension.contDiffOn_extension.contDiffAt (radiusExtension.isOpen_neighborhood.mem_nhds hqRadius))
    (gradientExtension.contDiffOn_extension.contDiffAt (gradientExtension.isOpen_neighborhood.mem_nhds hqGradient))
    hqSmall, ?_⟩
  intro hq
  simp only [exponentialMap, radiusExtension.agrees ⟨hq.1, hqRadius⟩,
    gradientExtension.agrees ⟨hq.1, hqGradient⟩]

theorem hasSmoothLocalExtensionOn_linearLiftFormula {X : Set E}
    (f : E → E) (D : E → E →L[ℝ] E)
    (hf : HasSmoothLocalExtensionOn X f) (hD : HasSmoothLocalExtensionOn X D)
    (T : X → E ≃L[ℝ] E) (hvalue : ∀ x : X, D x = (T x : E →L[ℝ] E)) :
    HasSmoothLocalExtensionOn (X ×ˢ {n : E | ‖n‖ = 1}) (linearLiftFormula f D) := by
  apply hasSmoothLocalExtensionOn_of_eventually_contDiffAt
  intro p hp
  obtain ⟨mapExtension⟩ := hf p.1 hp.1
  obtain ⟨derivativeExtension⟩ := hD p.1 hp.1
  have hderivativeAt := derivativeExtension.contDiffOn_extension.contDiffAt
    (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood)
  have hderivativeValue : derivativeExtension.extension p.1 = (T ⟨p.1, hp.1⟩ : E →L[ℝ] E) :=
    (derivativeExtension.agrees ⟨hp.1, derivativeExtension.mem_neighborhood⟩).trans (hvalue ⟨p.1, hp.1⟩)
  have hunit : IsUnit (derivativeExtension.extension p.1) := by
    rw [hderivativeValue]
    exact (T ⟨p.1, hp.1⟩).toUnit.isUnit
  have hinverse : ContDiffAt ℝ ∞
      (fun operator : E →L[ℝ] E => Ring.inverse operator) (derivativeExtension.extension p.1) := by
    simpa only [hunit.unit_spec] using (contDiffAt_ringInverse ℝ hunit.unit :
      ContDiffAt ℝ ∞ Ring.inverse (hunit.unit : E →L[ℝ] E))
  have hderivativeOnProduct : ContDiffAt ℝ ∞
      (fun q : E × E => derivativeExtension.extension q.1) p :=
    hderivativeAt.comp p contDiffAt_fst
  have hinverseOnProduct : ContDiffAt ℝ ∞
      (fun q : E × E => Ring.inverse (derivativeExtension.extension q.1)) p :=
    ContDiffAt.comp p
      (g := fun operator : E →L[ℝ] E => Ring.inverse operator)
      (f := fun q : E × E => derivativeExtension.extension q.1) hinverse hderivativeOnProduct
  have hadjoint : ContDiff ℝ ∞
      (fun operator : E →L[ℝ] E => ContinuousLinearMap.adjoint operator) :=
    (ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).contDiff
  have hoperatorAt : ContDiffAt ℝ ∞
      (fun q : E × E => ContinuousLinearMap.adjoint (Ring.inverse (derivativeExtension.extension q.1))) p :=
    hadjoint.contDiffAt.comp p hinverseOnProduct
  have hvectorAt : ContDiffAt ℝ ∞
      (fun q : E × E => ContinuousLinearMap.adjoint (Ring.inverse (derivativeExtension.extension q.1)) q.2) p :=
    hoperatorAt.clm_apply contDiffAt_snd
  have hne : ContinuousLinearMap.adjoint (Ring.inverse (derivativeExtension.extension p.1)) p.2 ≠ 0 := by
    rw [hderivativeValue, ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]
    exact linearMap_unit_ne_zero (inverseTranspose (T ⟨p.1, hp.1⟩)) hp.2
  refine ⟨linearLiftFormula mapExtension.extension derivativeExtension.extension, ?_⟩
  filter_upwards
    [continuous_fst.continuousAt.preimage_mem_nhds
      (mapExtension.isOpen_neighborhood.mem_nhds mapExtension.mem_neighborhood),
     continuous_fst.continuousAt.preimage_mem_nhds
      (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood),
     (hderivativeAt.continuousAt.comp continuous_fst.continuousAt).preimage_mem_nhds
      (Units.isOpen.mem_nhds hunit), hvectorAt.continuousAt.eventually_ne hne] with q hqMap hqD hqUnit hqNe
  refine ⟨contDiffAt_linearLiftFormula_of_isUnit _ _ q
    (mapExtension.contDiffOn_extension.contDiffAt (mapExtension.isOpen_neighborhood.mem_nhds hqMap))
    (derivativeExtension.contDiffOn_extension.contDiffAt (derivativeExtension.isOpen_neighborhood.mem_nhds hqD))
    hqUnit hqNe, ?_⟩
  intro hq
  simp only [linearLiftFormula, mapExtension.agrees ⟨hq.1, hqMap⟩,
    derivativeExtension.agrees ⟨hq.1, hqD⟩]

theorem hasSmoothLocalExtensionOn_transposeLiftFormula {X : Set E}
    (f : E → E) (D : E → E →L[ℝ] E)
    (hf : HasSmoothLocalExtensionOn X f) (hD : HasSmoothLocalExtensionOn X D)
    (T : X → E ≃L[ℝ] E) (hvalue : ∀ x : X, D x = (T x : E →L[ℝ] E)) :
    HasSmoothLocalExtensionOn (X ×ˢ {n : E | ‖n‖ = 1}) (transposeLiftFormula f D) := by
  apply hasSmoothLocalExtensionOn_of_eventually_contDiffAt
  intro p hp
  obtain ⟨mapExtension⟩ := hf p.1 hp.1
  obtain ⟨derivativeExtension⟩ := hD p.1 hp.1
  have hderivativeAt := derivativeExtension.contDiffOn_extension.contDiffAt
    (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood)
  have hvectorAt : ContDiffAt ℝ ∞
      (fun q : E × E => ContinuousLinearMap.adjoint (derivativeExtension.extension q.1) q.2) p :=
    ((ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).contDiff.contDiffAt.comp p
      (hderivativeAt.comp p contDiffAt_fst)).clm_apply contDiffAt_snd
  have hne : ContinuousLinearMap.adjoint (derivativeExtension.extension p.1) p.2 ≠ 0 := by
    rw [derivativeExtension.agrees ⟨hp.1, derivativeExtension.mem_neighborhood⟩, hvalue ⟨p.1, hp.1⟩]
    exact linearMap_unit_ne_zero (inverseTranspose (T ⟨p.1, hp.1⟩)).symm hp.2
  refine ⟨transposeLiftFormula mapExtension.extension derivativeExtension.extension, ?_⟩
  filter_upwards
    [continuous_fst.continuousAt.preimage_mem_nhds
      (mapExtension.isOpen_neighborhood.mem_nhds mapExtension.mem_neighborhood),
     continuous_fst.continuousAt.preimage_mem_nhds
      (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood),
     hvectorAt.continuousAt.eventually_ne hne] with q hqMap hqD hqNe
  have hvector : ContDiffAt ℝ ∞
      (fun t : E × E => ContinuousLinearMap.adjoint (derivativeExtension.extension t.1) t.2) q :=
    ((ContinuousLinearMap.adjoint : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E)).contDiff.contDiffAt.comp q
      ((derivativeExtension.contDiffOn_extension.contDiffAt
        (derivativeExtension.isOpen_neighborhood.mem_nhds hqD)).comp q contDiffAt_fst)).clm_apply contDiffAt_snd
  refine ⟨((mapExtension.contDiffOn_extension.contDiffAt
    (mapExtension.isOpen_neighborhood.mem_nhds hqMap)).comp q contDiffAt_fst).prodMk
      (((hvector.norm ℝ hqNe).inv (norm_ne_zero_iff.mpr hqNe)).smul hvector), ?_⟩
  intro hq
  simp only [transposeLiftFormula, mapExtension.agrees ⟨hq.1, hqMap⟩,
    derivativeExtension.agrees ⟨hq.1, hqD⟩]

variable {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.hasSmoothLocalExtensionOn_mapDerivativeOnAmbient
    (system : SetValuedSystem (E := E) r s)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map) :
    HasSmoothLocalExtensionOn system.domain system.mapDerivativeOnAmbient :=
  hmap.derivative_map system.diffeomorphism.forward_extension system.regular_closed system.map_order_pos
    (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) _ system.mapDerivativeOnAmbient_apply

theorem SetValuedSystem.hasSmoothLocalExtensionOn_linearLiftOnAmbient
    (system : SetValuedSystem (E := E) r s)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map) :
    HasSmoothLocalExtensionOn (system.domain ×ˢ {n : E | ‖n‖ = 1}) system.linearLiftOnAmbient :=
  hasSmoothLocalExtensionOn_linearLiftFormula _ _ hmap
    (system.hasSmoothLocalExtensionOn_mapDerivativeOnAmbient hmap)
    system.derivativeEquiv system.mapDerivativeOnAmbient_eq_derivativeEquiv

theorem SetValuedSystem.hasSmoothLocalExtensionOn_linearLiftInverseOnAmbient
    (system : SetValuedSystem (E := E) r s)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse) :
    HasSmoothLocalExtensionOn ((system.map '' system.domain) ×ˢ {n : E | ‖n‖ = 1})
      system.linearLiftInverseOnAmbient := by
  apply hasSmoothLocalExtensionOn_transposeLiftFormula _ _ hinverse
    ((system.hasSmoothLocalExtensionOn_mapDerivativeOnAmbient hmap).comp hinverse
      system.diffeomorphism.inverse_mapsTo)
    (fun y => system.derivativeEquiv ⟨system.diffeomorphism.inverse y, system.diffeomorphism.inverse_mapsTo y.property⟩)
  intro y
  exact system.mapDerivativeOnAmbient_eq_derivativeEquiv
    ⟨system.diffeomorphism.inverse y, system.diffeomorphism.inverse_mapsTo y.property⟩

theorem SetValuedSystem.hasSmoothLocalExtensionOn_boundaryFormulaOnAmbient
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius) :
    HasSmoothLocalExtensionOn (system.domain ×ˢ {n : E | ‖n‖ = 1}) system.boundaryFormulaOnAmbient := by
  have hgradient : HasSmoothLocalExtensionOn system.domain system.radiusGradientOnAmbient := by
    apply hradius.derivative_map system.radius_extension system.regular_closed system.radius_order_pos
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    intro y
    exact system.radiusGradientOnAmbient_apply y
  exact ((hasSmoothLocalExtensionOn_exponentialMap _ _ hradius hgradient
    hcontraction.norm_radiusGradientOnAmbient).mono_domain
      (fun _ hp => ⟨hp.1, mem_univ _⟩)).comp
    (system.hasSmoothLocalExtensionOn_linearLiftOnAmbient hmap) system.linearLiftOnAmbient_mapsTo

end BoundedUncertainty

