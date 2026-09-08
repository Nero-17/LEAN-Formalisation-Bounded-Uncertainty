import BoundedUncertainty.MaximizerGeometry
import BoundedUncertainty.BoundaryMap
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
Backward transport of maximizing gradients in Theorem 4.10. All smooth maps
used below are local representatives supplied by the system; smoothness of
intermediate set boundaries is unnecessary.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem normalize_positive_smul (v : E) (coefficient : ℝ) (hpositive : 0 < coefficient) :
    ‖coefficient • v‖⁻¹ • (coefficient • v) = ‖v‖⁻¹ • v := by
  rw [norm_smul, Real.norm_of_nonneg hpositive.le, mul_inv_rev, smul_smul, mul_assoc,
    inv_mul_cancel₀ (ne_of_gt hpositive), mul_one]

omit [CompleteSpace E] in
theorem normalizedLinearMap_normalize (T : E ≃L[ℝ] E) (v : E) (hv : v ≠ 0) :
    normalizedLinearMap T (‖v‖⁻¹ • v) = ‖T v‖⁻¹ • T v := by
  simp only [normalizedLinearMap, map_smul]
  exact normalize_positive_smul (T v) ‖v‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hv))

/-- Chain rule for the fixed-direction pullback, before choosing local representatives. -/
theorem hasGradientAt_maximizer_pullback
    (mapRepresentative : E → E) (radiusRepresentative G : E → ℝ)
    (a v radiusGradient : E) (coefficient : ℝ) (derivative : E →L[ℝ] E)
    (hv : ‖v‖ = 1)
    (hmap : HasFDerivAt mapRepresentative derivative a)
    (hradius : HasGradientAt radiusRepresentative radiusGradient (mapRepresentative a))
    (hG : HasGradientAt G (coefficient • v)
      (mapRepresentative a + radiusRepresentative (mapRepresentative a) • v)) :
    HasGradientAt
      (fun b => G (mapRepresentative b + radiusRepresentative (mapRepresentative b) • v))
      (coefficient • ContinuousLinearMap.adjoint derivative (v + radiusGradient)) a := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hchain := hG.hasFDerivAt.comp a
    (hmap.add ((hradius.hasFDerivAt.comp a hmap).smul_const v))
  convert hchain using 1
  ext w
  simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left, hv]

variable {r s : ℕ}

/-- The unit input normal reversing the fixed output direction at a given base point. -/
noncomputable def SetValuedSystem.backwardNormal
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (a : system.domain) (v : {v : E // ‖v‖ = 1}) : {v : E // ‖v‖ = 1} :=
  (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv a))).symm
    ⟨‖(v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩‖⁻¹ •
      ((v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩),
      norm_smul_inv_norm (unit_add_gradient_ne_zero _ _
        (hcontraction ⟨system.map a, system.map_into_domain a.property⟩) v.property)⟩

/-- The backward direction is the normalized transpose differential in the paper. -/
theorem SetValuedSystem.backwardNormal_formula
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (a : system.domain) (v : {v : E // ‖v‖ = 1}) :
    (system.backwardNormal hcontraction a v : E) =
      ‖ContinuousLinearMap.adjoint (system.derivativeEquiv a : E →L[ℝ] E)
        ((v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩)‖⁻¹ •
      ContinuousLinearMap.adjoint (system.derivativeEquiv a : E →L[ℝ] E)
        ((v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩) := by
  change normalizedLinearMap (inverseTranspose (system.derivativeEquiv a)).symm
    (‖(v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩‖⁻¹ •
      ((v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩)) = _
  rw [normalizedLinearMap_normalize _ _ (unit_add_gradient_ne_zero _ _
    (hcontraction ⟨system.map a, system.map_into_domain a.property⟩) v.property)]
  rfl

/-- Direct substitution in the actual beta, including zero-radius fibres. -/
theorem SetValuedSystem.boundaryMap_backwardNormal
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (a : system.domain) (v : {v : E // ‖v‖ = 1}) :
    (((system.boundaryMap hcontraction (a, system.backwardNormal hcontraction a v)).1 : E),
      ((system.boundaryMap hcontraction (a, system.backwardNormal hcontraction a v)).2 : E)) =
      (system.map a + system.radius (system.map a) • (v : E), (v : E)) := by
  have hlinear : system.linearLift (a, system.backwardNormal hcontraction a v) =
      (⟨system.map a, system.map_into_domain a.property⟩,
        ⟨‖(v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩‖⁻¹ •
          ((v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩),
          norm_smul_inv_norm (unit_add_gradient_ne_zero _ _
            (hcontraction ⟨system.map a, system.map_into_domain a.property⟩) v.property)⟩) := by
    apply Prod.ext
    · rfl
    · exact (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv a))).apply_symm_apply _
  change ((system.exponentialLift hcontraction
    (system.linearLift (a, system.backwardNormal hcontraction a v))).1,
    ((system.exponentialLift hcontraction
      (system.linearLift (a, system.backwardNormal hcontraction a v))).2 : E)) = _
  rw [hlinear]
  change (system.map a + system.radius (system.map a) •
    normalUpdate (system.radiusGradientOnAmbient (system.map a))
      (‖(v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩‖⁻¹ •
        ((v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩)),
    normalUpdate (system.radiusGradientOnAmbient (system.map a))
      (‖(v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩‖⁻¹ •
        ((v : E) + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩))) = _
  rw [system.radiusGradientOnAmbient_apply ⟨system.map a, system.map_into_domain a.property⟩,
    normalUpdate_normalize_add_gradient _ _
      (hcontraction ⟨system.map a, system.map_into_domain a.property⟩) v.property]

/-- Invertibility and contraction make the unnormalized pulled-back direction nonzero. -/
theorem SetValuedSystem.adjoint_add_radiusGradient_ne_zero
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (a : system.domain) (v : E) (hv : ‖v‖ = 1) :
    ContinuousLinearMap.adjoint (system.derivativeEquiv a : E →L[ℝ] E)
      (v + system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩) ≠ 0 := by
  intro hzero
  apply unit_add_gradient_ne_zero _ _
    (hcontraction ⟨system.map a, system.map_into_domain a.property⟩) hv
  apply (inverseTranspose (system.derivativeEquiv a)).symm.injective
  simpa only [inverseTranspose_symm_apply, map_zero] using hzero

omit [CompleteSpace E] in
/-- The fixed-direction selection belongs to the actual set-valued image. -/
theorem SetValuedSystem.fixedDirection_mem_setValuedImage
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (a : E) (ha : a ∈ A) (v : E) (hv : ‖v‖ = 1) :
    system.map a + system.radius (system.map a) • v ∈
      setValuedImage system.map system.radius A := by
  apply Set.mem_iUnion_of_mem a
  apply Set.mem_iUnion_of_mem ha
  have hnonnegative := system.radius_nonneg _ (system.map_into_domain (hA ha))
  simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg hnonnegative, hv, mul_one, le_refl]

omit [CompleteSpace E] in
/-- A global maximum remains global for the actual fixed-direction pullback. -/
theorem SetValuedSystem.isMaxOn_fixedDirection_pullback
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (a x : E) (v : E) (hv : ‖v‖ = 1) (G : E → ℝ)
    (hmax : IsMaxOn G (setValuedImage system.map system.radius A) x)
    (hposition : x = system.map a + system.radius (system.map a) • v) :
    IsMaxOn (fun b => G (system.map b + system.radius (system.map b) • v)) A a := by
  intro b hb
  change G (system.map b + system.radius (system.map b) • v) ≤
    G (system.map a + system.radius (system.map a) • v)
  rw [← hposition]
  exact hmax (system.fixedDirection_mem_setValuedImage A hA b hb v hv)

/-- One maximization step uses local representatives and needs no smooth boundary of A.
The returned C1 function agrees locally on A with the actual fixed-direction
pullback. It is a local maximizer, which suffices for the iterative argument. -/
theorem SetValuedSystem.exists_local_maximizer_pullback
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (a : system.domain) (ha : (a : E) ∈ A) (x : E)
    (hx : x ∈ Metric.closedBall (system.map a) (system.radius (system.map a)))
    (G : E → ℝ) (gradient : E) (hG : ContDiffAt ℝ 1 G x)
    (hgradient : HasGradientAt G gradient x) (hnonzero : gradient ≠ 0)
    (hmax : IsLocalMaxOn G (setValuedImage system.map system.radius A) x) :
    ∃ pullback : E → ℝ, ContDiffAt ℝ 1 pullback a ∧ IsLocalMaxOn pullback A a ∧
      HasGradientAt pullback
        (‖gradient‖ • ContinuousLinearMap.adjoint (system.derivativeEquiv a : E →L[ℝ] E)
          (‖gradient‖⁻¹ • gradient +
            system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩)) a ∧
      ∀ᶠ b in 𝓝 (a : E), b ∈ A → pullback b =
        G (system.map b + system.radius (system.map b) • (‖gradient‖⁻¹ • gradient)) := by
  have hunit : ‖‖gradient‖⁻¹ • gradient‖ = 1 := norm_smul_inv_norm hnonzero
  have hposition : x = system.map a + system.radius (system.map a) • (‖gradient‖⁻¹ • gradient) :=
    eq_center_add_radius_normalized_gradient_of_isLocalMaxOn_closedBall
      (system.map a) x (system.radius (system.map a))
      (system.radius_nonneg _ (system.map_into_domain a.property)) hx G gradient hgradient hnonzero
      (hmax.on_subset (Set.subset_iUnion₂_of_subset (a : E) ha Set.Subset.rfl))
  let mapExtension := Classical.choice (system.diffeomorphism.nonsingular a a.property)
  obtain ⟨radiusExtension⟩ := system.radius_extension (system.map a)
    (system.map_into_domain a.property)
  have hmapValue : mapExtension.extension a = system.map a :=
    mapExtension.agrees ⟨a.property, mapExtension.mem_neighborhood⟩
  have hradiusValue : radiusExtension.extension (system.map a) = system.radius (system.map a) :=
    radiusExtension.agrees ⟨system.map_into_domain a.property, radiusExtension.mem_neighborhood⟩
  have hmapSmooth : ContDiffAt ℝ 1 mapExtension.extension (a : E) :=
    (mapExtension.contDiffOn_extension.of_le (by exact_mod_cast system.map_order_pos)).contDiffAt
      (mapExtension.isOpen_neighborhood.mem_nhds mapExtension.mem_neighborhood)
  have hradiusSmooth : ContDiffAt ℝ 1 radiusExtension.extension (system.map a) :=
    (radiusExtension.contDiffOn_extension.of_le (by exact_mod_cast system.radius_order_pos)).contDiffAt
      (radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood)
  have hradiusGradient : HasGradientAt radiusExtension.extension
      (system.radiusGradient ⟨system.map a, system.map_into_domain a.property⟩) (system.map a) := by
    rw [system.radiusGradient_eq_extension system.radius_order_pos radiusExtension
      ⟨system.map a, system.map_into_domain a.property⟩ radiusExtension.mem_neighborhood]
    exact (hradiusSmooth.differentiableAt one_ne_zero).hasGradientAt
  have hrepresentativePosition : mapExtension.extension a +
      radiusExtension.extension (mapExtension.extension a) • (‖gradient‖⁻¹ • gradient) = x := by
    rw [hmapValue, hradiusValue]
    exact hposition.symm
  have hradiusAtMap : ContDiffAt ℝ 1 radiusExtension.extension (mapExtension.extension a) :=
    hmapValue.symm ▸ hradiusSmooth
  have hpositionSmooth : ContDiffAt ℝ 1
      (fun b => mapExtension.extension b +
        radiusExtension.extension (mapExtension.extension b) • (‖gradient‖⁻¹ • gradient)) (a : E) :=
    hmapSmooth.add ((hradiusAtMap.comp (a : E) hmapSmooth).smul contDiffAt_const)
  have hagrees : ∀ᶠ b in 𝓝 (a : E), b ∈ A →
      G (mapExtension.extension b +
        radiusExtension.extension (mapExtension.extension b) • (‖gradient‖⁻¹ • gradient)) =
      G (system.map b + system.radius (system.map b) • (‖gradient‖⁻¹ • gradient)) := by
    have hradiusNeighborhood : radiusExtension.neighborhood ∈ 𝓝 (mapExtension.extension a) := by
      rw [hmapValue]
      exact radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood
    filter_upwards [mapExtension.isOpen_neighborhood.mem_nhds mapExtension.mem_neighborhood,
      hmapSmooth.continuousAt.preimage_mem_nhds hradiusNeighborhood] with b hbMap hbRadius hb
    have hmapAgreement := mapExtension.agrees ⟨hA hb, hbMap⟩
    have hradiusAgreement := radiusExtension.agrees
      ⟨system.map_into_domain (hA hb), hmapAgreement ▸ hbRadius⟩
    rw [hmapAgreement, hradiusAgreement]
  refine ⟨fun b => G (mapExtension.extension b +
    radiusExtension.extension (mapExtension.extension b) • (‖gradient‖⁻¹ • gradient)),
    ?_, ?_, ?_, hagrees⟩
  · exact (hrepresentativePosition.symm ▸ hG).comp (a : E) hpositionSmooth
  · have hmapContinuous := system.diffeomorphism.forward_extension.continuousOn.mono hA
    have hradiusContinuous := system.radius_extension.continuousOn.comp hmapContinuous
      (fun _ hb => system.map_into_domain (hA hb))
    have hactualMax : IsLocalMaxOn
        (fun b => G (system.map b + system.radius (system.map b) • (‖gradient‖⁻¹ • gradient)))
        A (a : E) := by
      have hmaxAt : IsLocalMaxOn G (setValuedImage system.map system.radius A)
          (system.map a + system.radius (system.map a) • (‖gradient‖⁻¹ • gradient)) :=
        hposition ▸ hmax
      exact hmaxAt.comp_continuousOn
        (g := fun b => system.map b + system.radius (system.map b) • (‖gradient‖⁻¹ • gradient))
        (fun b hb => system.fixedDirection_mem_setValuedImage A hA b hb _ hunit)
        (hmapContinuous.add (hradiusContinuous.smul continuousOn_const)) ha
    apply hactualMax.congr _ ha
    filter_upwards [hagrees.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with b hb hbA
    exact (hb hbA).symm
  · apply hasGradientAt_maximizer_pullback mapExtension.extension radiusExtension.extension G
      (a : E) _ _ ‖gradient‖ (system.derivativeEquiv a : E →L[ℝ] E) hunit
      mapExtension.hasFDerivAt_extension
    · exact hmapValue.symm ▸ hradiusGradient
    · rw [hrepresentativePosition]
      simpa only [smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnonzero), one_smul] using hgradient

/-- A complete one-step certificate for induction on local maximizing gradients. -/
theorem SetValuedSystem.exists_predecessor_local_maximizer
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (x : system.domain)
    (hx : (x : E) ∈ setValuedImage system.map system.radius A)
    (G : E → ℝ) (gradient : E) (hG : ContDiffAt ℝ 1 G (x : E))
    (hgradient : HasGradientAt G gradient (x : E)) (hnonzero : gradient ≠ 0)
    (hmax : IsLocalMaxOn G (setValuedImage system.map system.radius A) (x : E)) :
    ∃ a : system.domain, (a : E) ∈ A ∧
      ∃ (pullback : E → ℝ) (pullbackGradient : E) (hpullback : pullbackGradient ≠ 0),
        ContDiffAt ℝ 1 pullback (a : E) ∧ IsLocalMaxOn pullback A (a : E) ∧
        HasGradientAt pullback pullbackGradient (a : E) ∧
        system.boundaryMap hcontraction
          (a, ⟨‖pullbackGradient‖⁻¹ • pullbackGradient, norm_smul_inv_norm hpullback⟩) =
          (x, ⟨‖gradient‖⁻¹ • gradient, norm_smul_inv_norm hnonzero⟩) := by
  obtain ⟨a, ha, hxball⟩ : ∃ a ∈ A,
      (x : E) ∈ Metric.closedBall (system.map a) (system.radius (system.map a)) := by
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    obtain ⟨haA, hxball⟩ := Set.mem_iUnion.mp ha
    exact ⟨a, haA, hxball⟩
  obtain ⟨pullback, hsmooth, hmaximum, hderivative, _⟩ :=
    system.exists_local_maximizer_pullback A hA ⟨a, hA ha⟩ ha x hxball
      G gradient hG hgradient hnonzero hmax
  have hunit : ‖‖gradient‖⁻¹ • gradient‖ = 1 := norm_smul_inv_norm hnonzero
  have hpullback : ‖gradient‖ •
      ContinuousLinearMap.adjoint (system.derivativeEquiv ⟨a, hA ha⟩ : E →L[ℝ] E)
        (‖gradient‖⁻¹ • gradient + system.radiusGradient ⟨system.map a,
          system.map_into_domain (hA ha)⟩) ≠ 0 :=
    smul_ne_zero (norm_ne_zero_iff.mpr hnonzero)
      (system.adjoint_add_radiusGradient_ne_zero hcontraction ⟨a, hA ha⟩ _ hunit)
  refine ⟨⟨a, hA ha⟩, ha, pullback, _, hpullback, hsmooth, hmaximum, hderivative, ?_⟩
  have hnormal :
      (⟨‖‖gradient‖ •
        ContinuousLinearMap.adjoint (system.derivativeEquiv ⟨a, hA ha⟩ : E →L[ℝ] E)
          (‖gradient‖⁻¹ • gradient + system.radiusGradient ⟨system.map a,
            system.map_into_domain (hA ha)⟩)‖⁻¹ •
        (‖gradient‖ • ContinuousLinearMap.adjoint
          (system.derivativeEquiv ⟨a, hA ha⟩ : E →L[ℝ] E)
            (‖gradient‖⁻¹ • gradient + system.radiusGradient ⟨system.map a,
              system.map_into_domain (hA ha)⟩)), norm_smul_inv_norm hpullback⟩ :
        {v : E // ‖v‖ = 1}) =
      system.backwardNormal hcontraction ⟨a, hA ha⟩ ⟨‖gradient‖⁻¹ • gradient, hunit⟩ := by
    apply Subtype.ext
    dsimp only
    rw [normalize_positive_smul _ _ (norm_pos_iff.mpr hnonzero),
      system.backwardNormal_formula]
  rw [hnormal]
  have hcoordinates := system.boundaryMap_backwardNormal hcontraction
    ⟨a, hA ha⟩ ⟨‖gradient‖⁻¹ • gradient, hunit⟩
  have hposition : (x : E) = system.map a +
      system.radius (system.map a) • (‖gradient‖⁻¹ • gradient) :=
    eq_center_add_radius_normalized_gradient_of_isLocalMaxOn_closedBall
      (system.map a) x (system.radius (system.map a))
      (system.radius_nonneg _ (system.map_into_domain (hA ha))) hxball
      G gradient hgradient hnonzero
      (hmax.on_subset (Set.subset_iUnion₂_of_subset a ha Set.Subset.rfl))
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg Prod.fst hcoordinates).trans hposition.symm
  · apply Subtype.ext
    exact congrArg Prod.snd hcoordinates

end BoundedUncertainty
