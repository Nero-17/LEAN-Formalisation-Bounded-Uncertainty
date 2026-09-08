import BoundedUncertainty.BundleDifferential

/-!
# The nonsingular intrinsic differential of the genuine boundary map

For `r,s ≥ 2`, every C1 local extension of the actual boundary formula has
the same differential on the source bundle tangent space.  Its restriction
is a continuous linear equivalence onto the output bundle tangent space.
No inverse identity is asserted for the auxiliary extensions off the bundle.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- A C1 local inverse of the actual beta formula forces every C1 source
extension to have a nonsingular intrinsic differential. -/
theorem SetValuedSystem.exists_boundaryTangentEquiv_of_inverse_extension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hinverseExtension : HasLocalExtensionOn 1 (Set.range system.boundaryFormula)
      (system.boundaryInverseOnAmbient hcontraction))
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (extension : LocalExtensionAt 1 (system.domain ×ˢ {n : E | ‖n‖ = 1})
      system.boundaryFormulaOnAmbient p) :
    ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
        bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
      ∀ v : bundleTangentSpace p.2,
        (differential v : E × E) = fderiv ℝ extension.extension p v := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  have hsource : system.boundaryFormulaOnAmbient p ∈ Set.range system.boundaryFormula :=
    ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩),
      (system.boundaryFormulaOnAmbient_apply (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)).symm⟩
  obtain ⟨inverseExtension⟩ := hinverseExtension (system.boundaryFormulaOnAmbient p) hsource
  have hvalue : extension.extension p = system.boundaryFormulaOnAmbient p :=
    extension.agrees ⟨hp, extension.mem_neighborhood⟩
  have hforward : ContDiffAt ℝ 1 extension.extension p :=
    extension.contDiffOn_extension.contDiffAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  have hinverse : ContDiffAt ℝ 1 inverseExtension.extension (extension.extension p) := by
    rw [hvalue]
    exact inverseExtension.contDiffOn_extension.contDiffAt
      (inverseExtension.isOpen_neighborhood.mem_nhds inverseExtension.mem_neighborhood)
  have hunit : ∀ᶠ q in 𝓝 p,
      q ∈ system.domain ×ˢ {n : E | ‖n‖ = 1} → ‖(extension.extension q).2‖ = 1 := by
    filter_upwards [extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood]
      with q hqU hq
    rw [extension.agrees ⟨hq, hqU⟩,
      system.boundaryFormulaOnAmbient_eq_boundaryMap hcontraction
        (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)]
    exact (system.boundaryMap hcontraction (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)).2.property
  have hleft : ∀ᶠ q in 𝓝 p,
      q ∈ system.domain ×ˢ {n : E | ‖n‖ = 1} →
        inverseExtension.extension (extension.extension q) = q := by
    have htargetNeighborhood : inverseExtension.neighborhood ∈ 𝓝 (extension.extension p) := by
      rw [hvalue]
      exact inverseExtension.isOpen_neighborhood.mem_nhds inverseExtension.mem_neighborhood
    filter_upwards [extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood,
      hforward.continuousAt.preimage_mem_nhds htargetNeighborhood] with q hqForward hqInverse hq
    have hqValue := extension.agrees ⟨hq, hqForward⟩
    have hqRange : system.boundaryFormulaOnAmbient q ∈ Set.range system.boundaryFormula :=
      ⟨(⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩),
        (system.boundaryFormulaOnAmbient_apply (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)).symm⟩
    rw [hqValue, inverseExtension.agrees ⟨hqRange, hqValue ▸ hqInverse⟩,
      system.boundaryFormulaOnAmbient_apply (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩),
      system.boundaryInverseOnAmbient_formula]
  have hregular : system.domain ⊆ closure (interior system.domain) := by
    rw [system.regular_closed]
  have hresult : ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
        bundleTangentSpace (extension.extension p).2,
      ∀ v : bundleTangentSpace p.2,
        (differential v : E × E) = fderiv ℝ extension.extension p v :=
    ⟨bundleTangentEquivOfLocalInverse hregular hp.1 hp.2 hforward hinverse hunit hleft,
      fun v => bundleTangentEquivOfLocalInverse_apply hregular hp.1 hp.2
        hforward hinverse hunit hleft v⟩
  have hnormalValue : (extension.extension p).2 = (system.boundaryFormulaOnAmbient p).2 :=
    congrArg Prod.snd hvalue
  rw [← hnormalValue]
  exact hresult

/-- Every local C1 extension of the genuine beta formula has a nonsingular
differential when the original finite orders satisfy `r,s ≥ 2`. -/
theorem SetValuedSystem.exists_boundaryTangentEquiv
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (extension : LocalExtensionAt 1 (system.domain ×ˢ {n : E | ‖n‖ = 1})
      system.boundaryFormulaOnAmbient p) :
    ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
        bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
      ∀ v : bundleTangentSpace p.2,
        (differential v : E × E) = fderiv ℝ extension.extension p v :=
  system.exists_boundaryTangentEquiv_of_inverse_extension hcontraction
    ((system.hasLocalExtensionOn_boundaryInverseOnAmbient hcontraction).of_le
      (by omega : 1 ≤ min r s - 1)) p hp extension

/-- The complete nonsingularity assertion, including existence of the local
extension, follows from the original system assumptions when `r,s ≥ 2`. -/
theorem SetValuedSystem.exists_nonsingular_boundaryExtension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    ∃ extension : LocalExtensionAt 1 (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
          bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
        ∀ v : bundleTangentSpace p.2,
          (differential v : E × E) = fderiv ℝ extension.extension p v := by
  obtain ⟨extension⟩ :=
    ((system.hasLocalExtensionOn_boundaryFormulaOnAmbient hcontraction).of_le
      (by omega : 1 ≤ min r s - 1)) p hp
  exact ⟨extension, system.exists_boundaryTangentEquiv hcontraction hr hs p hp extension⟩

/-- The intrinsic beta differential does not depend on the local ambient extension. -/
theorem SetValuedSystem.boundaryTangentDerivative_eq_extension
    (system : SetValuedSystem (E := E) r s)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (first second : LocalExtensionAt 1 (system.domain ×ˢ {n : E | ‖n‖ = 1})
      system.boundaryFormulaOnAmbient p) (v : bundleTangentSpace p.2) :
    fderiv ℝ first.extension p v = fderiv ℝ second.extension p v := by
  have hfirst : ContDiffAt ℝ 1 first.extension p := first.contDiffOn_extension.contDiffAt
    (first.isOpen_neighborhood.mem_nhds first.mem_neighborhood)
  have hsecond : ContDiffAt ℝ 1 second.extension p := second.contDiffOn_extension.contDiffAt
    (second.isOpen_neighborhood.mem_nhds second.mem_neighborhood)
  have hzero : ∀ᶠ q in 𝓝 p,
      q ∈ system.domain ×ˢ {n : E | ‖n‖ = 1} → first.extension q - second.extension q = 0 := by
    filter_upwards [first.isOpen_neighborhood.mem_nhds first.mem_neighborhood,
      second.isOpen_neighborhood.mem_nhds second.mem_neighborhood] with q hqFirst hqSecond hq
    rw [first.agrees ⟨hq, hqFirst⟩, second.agrees ⟨hq, hqSecond⟩, sub_self]
  have hregular : system.domain ⊆ closure (interior system.domain) := by
    rw [system.regular_closed]
  have hderivative := fderiv_bundle_eq_zero_of_vanishes hregular hp.1 hp.2
    (hfirst.sub hsecond) hzero v.val.1 v.val.2 v.property
  have hchain := (hfirst.differentiableAt one_ne_zero).hasFDerivAt.sub
    (hsecond.differentiableAt one_ne_zero).hasFDerivAt
  change fderiv ℝ (first.extension - second.extension) p v = 0 at hderivative
  rw [hchain.fderiv] at hderivative
  exact sub_eq_zero.mp hderivative

end BoundedUncertainty
