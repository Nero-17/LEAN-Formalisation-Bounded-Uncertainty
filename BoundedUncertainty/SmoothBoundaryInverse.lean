import BoundedUncertainty.SmoothBoundaryForward
import BoundedUncertainty.SmoothExponentialInverse
import BoundedUncertainty.SmoothSphereExtension
import BoundedUncertainty.BoundaryDifferential

/-!
# The smooth boundary homeomorphism with a nonsingular intrinsic differential

Each smooth hypothesis supplies one fixed C-infinity neighborhood extension
at each point. Both beta and its actual inverse have such extensions. The
intrinsic differential is nonsingular even if the finite orders in the
underlying system are only one, because the smooth inverse supplies C1 data.
-/

namespace BoundedUncertainty

open Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

theorem SetValuedSystem.hasSmoothLocalExtensionOn_boundaryInverseOnAmbient
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse) :
    HasSmoothLocalExtensionOn (Set.range system.boundaryFormula)
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
  have hcomposed := (system.hasSmoothLocalExtensionOn_linearLiftInverseOnAmbient hmap hinverse).comp
    hintermediate (system.linearLiftOnAmbient_mapsTo_image.comp
      (system.boundaryInverseOnAmbient_mapsTo hcontraction))
  apply hcomposed.congr
  intro p hp
  exact system.linearLiftInverseOnAmbient_linearLiftOnAmbient _
    (system.boundaryInverseOnAmbient_mapsTo hcontraction hp)

/-- One fixed smooth sphere-valued extension of the actual forward formula. -/
theorem SetValuedSystem.exists_smooth_sphere_boundaryExtension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    ∃ extension : SmoothLocalExtensionAt (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1 := by
  apply (system.hasSmoothLocalExtensionOn_boundaryFormulaOnAmbient hcontraction hmap hradius).exists_sphere_valued_extension _ p hp
  intro q hq
  rw [system.boundaryFormulaOnAmbient_eq_boundaryMap hcontraction
    (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)]
  exact (system.boundaryMap hcontraction (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)).2.property

/-- One fixed smooth sphere-valued extension of the actual inverse on its range. -/
theorem SetValuedSystem.exists_smooth_sphere_boundaryInverseExtension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse)
    (p : E × E) (hp : p ∈ Set.range system.boundaryFormula) :
    ∃ extension : SmoothLocalExtensionAt (Set.range system.boundaryFormula)
        (system.boundaryInverseOnAmbient hcontraction) p,
      ∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1 := by
  exact (system.hasSmoothLocalExtensionOn_boundaryInverseOnAmbient hcontraction hmap hradius hinverse).exists_sphere_valued_extension
      (fun q hq => (system.boundaryInverseOnAmbient_mapsTo hcontraction hq).2) p hp

/-- The smooth case includes the nonsingular intrinsic differential, without
requiring the declared finite base orders to be at least two. -/
theorem SetValuedSystem.exists_smooth_nonsingular_boundaryExtension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    ∃ extension : SmoothLocalExtensionAt (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
      ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
          bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
        ∀ v : bundleTangentSpace p.2,
          (differential v : E × E) = fderiv ℝ extension.extension p v := by
  obtain ⟨extension, hunit⟩ := system.exists_smooth_sphere_boundaryExtension
    hcontraction hmap hradius p hp
  exact ⟨extension, hunit, system.exists_boundaryTangentEquiv_of_inverse_extension hcontraction
    ((system.hasSmoothLocalExtensionOn_boundaryInverseOnAmbient hcontraction hmap hradius hinverse).toHasLocalExtensionOn 1) p hp (extension.toLocalExtensionAt 1)⟩

/-- Both directions are smoothly extendible, and beta is the actual topological embedding. -/
theorem SetValuedSystem.boundaryFormula_smooth_homeomorphism
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse) :
    IsEmbedding system.boundaryFormula ∧
      HasSmoothLocalExtensionOn (system.domain ×ˢ {n : E | ‖n‖ = 1}) system.boundaryFormulaOnAmbient ∧
      HasSmoothLocalExtensionOn (Set.range system.boundaryFormula)
        (system.boundaryInverseOnAmbient hcontraction) :=
  ⟨system.isEmbedding_boundaryFormula hcontraction,
    system.hasSmoothLocalExtensionOn_boundaryFormulaOnAmbient hcontraction hmap hradius,
    system.hasSmoothLocalExtensionOn_boundaryInverseOnAmbient hcontraction hmap hradius hinverse⟩

theorem SetValuedSystem.hasSmoothLocalExtensionOn_boundaryInverseOnAmbient_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse)
    (himage : system.map '' system.domain = system.domain) :
    HasSmoothLocalExtensionOn (system.domain ×ˢ {n : E | ‖n‖ = 1})
      (system.boundaryInverseOnAmbient hcontraction) := by
  rw [← system.range_boundaryFormula_of_image_eq_domain hcontraction himage]
  exact system.hasSmoothLocalExtensionOn_boundaryInverseOnAmbient hcontraction hmap hradius hinverse

end BoundedUncertainty
