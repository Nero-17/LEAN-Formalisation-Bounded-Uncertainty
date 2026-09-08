import BoundedUncertainty.SmoothBoundaryInverse

/-!
# Mixed finite and smooth regularity

All results retain the original system and its actual canonical derivatives.
A fixed smooth local witness is lowered to the finite order required by the
other component; no replacement system or change of the boundary map occurs.
-/

namespace BoundedUncertainty

open Set Topology

def LocalExtensionAt.of_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {order lowerOrder : ℕ}
    {X : Set E} {f : E → F} {x : E} (extension : LocalExtensionAt order X f x)
    (horder : lowerOrder ≤ order) : LocalExtensionAt lowerOrder X f x where
  neighborhood := extension.neighborhood
  isOpen_neighborhood := extension.isOpen_neighborhood
  mem_neighborhood := extension.mem_neighborhood
  extension := extension.extension
  contDiffOn_extension := extension.contDiffOn_extension.of_le (by exact_mod_cast horder)
  agrees := extension.agrees

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

theorem SetValuedSystem.hasLocalExtensionOn_boundaryFormulaOnAmbient_of_smooth_map
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map) :
    HasLocalExtensionOn (r - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
      system.boundaryFormulaOnAmbient :=
  (system.hasLocalExtensionOn_exponentialMap hcontraction).comp
    ((system.hasSmoothLocalExtensionOn_linearLiftOnAmbient hmap).toHasLocalExtensionOn (r - 1))
    system.linearLiftOnAmbient_mapsTo

theorem SetValuedSystem.hasLocalExtensionOn_boundaryInverseOnAmbient_of_smooth_map
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse) :
    HasLocalExtensionOn (r - 1) (Set.range system.boundaryFormula)
      (system.boundaryInverseOnAmbient hcontraction) := by
  have hintermediate := system.hasLocalExtensionOn_exponentialInverse_of_continuous hcontraction
    (system.linearLiftOnAmbient ∘ system.boundaryInverseOnAmbient hcontraction)
    (Set.range system.boundaryFormula)
    (system.hasLocalExtensionOn_linearLiftOnAmbient.continuousOn.comp
      (system.continuousOn_boundaryInverseOnAmbient hcontraction)
      (system.boundaryInverseOnAmbient_mapsTo hcontraction))
    (system.linearLiftOnAmbient_mapsTo.comp (system.boundaryInverseOnAmbient_mapsTo hcontraction))
    (system.boundaryFormulaOnAmbient_inverse hcontraction)
  have hcomposed := ((system.hasSmoothLocalExtensionOn_linearLiftInverseOnAmbient hmap hinverse).toHasLocalExtensionOn (r - 1)).comp
    hintermediate (system.linearLiftOnAmbient_mapsTo_image.comp
      (system.boundaryInverseOnAmbient_mapsTo hcontraction))
  apply hcomposed.congr
  intro p hp
  exact system.linearLiftInverseOnAmbient_linearLiftOnAmbient _
    (system.boundaryInverseOnAmbient_mapsTo hcontraction hp)

theorem SetValuedSystem.hasLocalExtensionOn_boundaryFormulaOnAmbient_of_smooth_radius
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius) :
    HasLocalExtensionOn (s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
      system.boundaryFormulaOnAmbient := by
  have hexponential := hasSmoothLocalExtensionOn_exponentialMap
    system.radius system.radiusGradientOnAmbient hradius
    (system.hasSmoothLocalExtensionOn_radiusGradientOnAmbient hradius)
    hcontraction.norm_radiusGradientOnAmbient
  exact ((hexponential.toHasLocalExtensionOn (s - 1)).mono_domain
    (fun _ hp => ⟨hp.1, Set.mem_univ _⟩)).comp
      system.hasLocalExtensionOn_linearLiftOnAmbient system.linearLiftOnAmbient_mapsTo

theorem SetValuedSystem.hasLocalExtensionOn_boundaryInverseOnAmbient_of_smooth_radius
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius) :
    HasLocalExtensionOn (s - 1) (Set.range system.boundaryFormula)
      (system.boundaryInverseOnAmbient hcontraction) := by
  have hintermediate := system.hasSmoothLocalExtensionOn_exponentialInverse_of_continuous
    hcontraction hradius
    (system.linearLiftOnAmbient ∘ system.boundaryInverseOnAmbient hcontraction)
    (Set.range system.boundaryFormula)
    (system.hasLocalExtensionOn_linearLiftOnAmbient.continuousOn.comp
      (system.continuousOn_boundaryInverseOnAmbient hcontraction)
      (system.boundaryInverseOnAmbient_mapsTo hcontraction))
    (system.linearLiftOnAmbient_mapsTo.comp (system.boundaryInverseOnAmbient_mapsTo hcontraction))
    (system.boundaryFormulaOnAmbient_inverse hcontraction)
  have hcomposed := system.hasLocalExtensionOn_linearLiftInverseOnAmbient.comp
    (hintermediate.toHasLocalExtensionOn (s - 1))
    (system.linearLiftOnAmbient_mapsTo_image.comp
      (system.boundaryInverseOnAmbient_mapsTo hcontraction))
  apply hcomposed.congr
  intro p hp
  exact system.linearLiftInverseOnAmbient_linearLiftOnAmbient _
    (system.boundaryInverseOnAmbient_mapsTo hcontraction hp)

/-- Radius order r and a smooth deterministic diffeomorphism give both
directions of beta order r-1 on the original source and actual range. -/
theorem SetValuedSystem.boundaryFormula_regular_homeomorphism_of_smooth_map
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse) :
    IsEmbedding system.boundaryFormula ∧
      HasLocalExtensionOn (r - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1}) system.boundaryFormulaOnAmbient ∧
      HasLocalExtensionOn (r - 1) (Set.range system.boundaryFormula)
        (system.boundaryInverseOnAmbient hcontraction) :=
  ⟨system.isEmbedding_boundaryFormula hcontraction,
    system.hasLocalExtensionOn_boundaryFormulaOnAmbient_of_smooth_map hcontraction hmap,
    system.hasLocalExtensionOn_boundaryInverseOnAmbient_of_smooth_map hcontraction hmap hinverse⟩

/-- A smooth radius and deterministic order s give both directions order s-1. -/
theorem SetValuedSystem.boundaryFormula_regular_homeomorphism_of_smooth_radius
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius) :
    IsEmbedding system.boundaryFormula ∧
      HasLocalExtensionOn (s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1}) system.boundaryFormulaOnAmbient ∧
      HasLocalExtensionOn (s - 1) (Set.range system.boundaryFormula)
        (system.boundaryInverseOnAmbient hcontraction) :=
  ⟨system.isEmbedding_boundaryFormula hcontraction,
    system.hasLocalExtensionOn_boundaryFormulaOnAmbient_of_smooth_radius hcontraction hradius,
    system.hasLocalExtensionOn_boundaryInverseOnAmbient_of_smooth_radius hcontraction hradius⟩

theorem SetValuedSystem.exists_nonsingular_boundaryExtension_of_smooth_map
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse)
    (hr : 2 ≤ r) (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    ∃ extension : LocalExtensionAt (r - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
          bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
        ∀ v : bundleTangentSpace p.2,
          (differential v : E × E) = fderiv ℝ extension.extension p v := by
  obtain ⟨extension⟩ := system.hasLocalExtensionOn_boundaryFormulaOnAmbient_of_smooth_map
    hcontraction hmap p hp
  exact ⟨extension, system.exists_boundaryTangentEquiv_of_inverse_extension hcontraction
    ((system.hasLocalExtensionOn_boundaryInverseOnAmbient_of_smooth_map hcontraction hmap hinverse).of_le (by omega))
    p hp (extension.of_le (by omega))⟩

theorem SetValuedSystem.exists_nonsingular_boundaryExtension_of_smooth_radius
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hs : 2 ≤ s) (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    ∃ extension : LocalExtensionAt (s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
          bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
        ∀ v : bundleTangentSpace p.2,
          (differential v : E × E) = fderiv ℝ extension.extension p v := by
  obtain ⟨extension⟩ := system.hasLocalExtensionOn_boundaryFormulaOnAmbient_of_smooth_radius
    hcontraction hradius p hp
  exact ⟨extension, system.exists_boundaryTangentEquiv_of_inverse_extension hcontraction
    ((system.hasLocalExtensionOn_boundaryInverseOnAmbient_of_smooth_radius hcontraction hradius).of_le (by omega))
    p hp (extension.of_le (by omega))⟩

end BoundedUncertainty
