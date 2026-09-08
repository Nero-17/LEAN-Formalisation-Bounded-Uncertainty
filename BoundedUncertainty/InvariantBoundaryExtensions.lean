import BoundedUncertainty.InvariantBoundaryRegularity
import BoundedUncertainty.MixedRegularity

/-!
# Sphere-valued extensions along invariant normal bundles

These interfaces complete the local extension convention for Corollary 4.7.
The forward witness agrees with the actual boundary map on the full state
bundle, and its differential is restricted to the full bundle tangent space.
No full-rank claim is made for arbitrary extensions agreeing only on the thin
outward normal bundle. Both finite and smooth witnesses take sphere values
throughout their open neighborhoods.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- A sphere-valued local extension of the actual forward map on the full state bundle. -/
theorem SetValuedSystem.exists_sphere_boundaryExtension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    ∃ extension : LocalExtensionAt (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1 := by
  obtain ⟨extension⟩ := system.hasLocalExtensionOn_boundaryFormulaOnAmbient hcontraction p hp
  apply extension.exists_sphere_valued_extension hp
  intro q hq
  rw [system.boundaryFormulaOnAmbient_eq_boundaryMap hcontraction
    (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)]
  exact (system.boundaryMap hcontraction (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)).2.property

/-- A sphere-valued local extension of the actual inverse on its actual range. -/
theorem SetValuedSystem.exists_sphere_boundaryInverseExtension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : E × E) (hp : p ∈ range system.boundaryFormula) :
    ∃ extension : LocalExtensionAt (min r s - 1) (range system.boundaryFormula)
        (system.boundaryInverseOnAmbient hcontraction) p,
      ∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1 := by
  obtain ⟨extension⟩ := system.hasLocalExtensionOn_boundaryInverseOnAmbient hcontraction p hp
  exact extension.exists_sphere_valued_extension hp
    (fun q hq => (system.boundaryInverseOnAmbient_mapsTo hcontraction hq).2)

/-- The same forward witness has the asserted higher order, sphere-valued
neighborhood, and nonsingular intrinsic differential on the full state bundle. -/
theorem SetValuedSystem.exists_regular_sphere_nonsingular_boundaryExtension
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    ∃ extension : LocalExtensionAt (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
      ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
          bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
        ∀ v : bundleTangentSpace p.2,
          (differential v : E × E) = fderiv ℝ extension.extension p v := by
  obtain ⟨extension, hunit⟩ := system.exists_sphere_boundaryExtension hcontraction p hp
  exact ⟨extension, hunit,
    system.exists_boundaryTangentEquiv hcontraction hr hs p hp (extension.of_le (by omega))⟩

/-- Finite sphere-valued forward and inverse witnesses at every point of any
invariant subset; the forward differential still uses full state-bundle data. -/
theorem SetValuedSystem.exists_regular_sphere_boundaryExtensions_on_invariant
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set (E × E)) (hB : B ⊆ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (hinvariant : system.boundaryFormulaOnAmbient '' B = B)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (p : E × E) (hp : p ∈ B) :
    ∃ extension : LocalExtensionAt (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ inverseExtension : LocalExtensionAt (min r s - 1) (range system.boundaryFormula)
          (system.boundaryInverseOnAmbient hcontraction) p,
        (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
        (∀ q ∈ inverseExtension.neighborhood, ‖(inverseExtension.extension q).2‖ = 1) ∧
        ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
            bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
          ∀ v : bundleTangentSpace p.2,
            (differential v : E × E) = fderiv ℝ extension.extension p v := by
  obtain ⟨extension, hunit, hdifferential⟩ :=
    system.exists_regular_sphere_nonsingular_boundaryExtension hcontraction hr hs p (hB hp)
  obtain ⟨inverseExtension, hinverseUnit⟩ := system.exists_sphere_boundaryInverseExtension
    hcontraction p (system.invariant_subset_range_boundaryFormula B hB hinvariant hp)
  exact ⟨extension, inverseExtension, hunit, hinverseUnit, hdifferential⟩

/-- The smooth version uses fixed C-infinity witnesses on single open neighborhoods. -/
theorem SetValuedSystem.exists_smooth_sphere_boundaryExtensions_on_invariant
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse)
    (B : Set (E × E)) (hB : B ⊆ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (hinvariant : system.boundaryFormulaOnAmbient '' B = B) (p : E × E) (hp : p ∈ B) :
    ∃ extension : SmoothLocalExtensionAt (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ inverseExtension : SmoothLocalExtensionAt (range system.boundaryFormula)
          (system.boundaryInverseOnAmbient hcontraction) p,
        (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
        (∀ q ∈ inverseExtension.neighborhood, ‖(inverseExtension.extension q).2‖ = 1) ∧
        ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
            bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
          ∀ v : bundleTangentSpace p.2,
            (differential v : E × E) = fderiv ℝ extension.extension p v := by
  obtain ⟨extension, hunit, hdifferential⟩ := system.exists_smooth_nonsingular_boundaryExtension
    hcontraction hmap hradius hinverse p (hB hp)
  obtain ⟨inverseExtension, hinverseUnit⟩ := system.exists_smooth_sphere_boundaryInverseExtension
    hcontraction hmap hradius hinverse p (system.invariant_subset_range_boundaryFormula B hB hinvariant hp)
  exact ⟨extension, inverseExtension, hunit, hinverseUnit, hdifferential⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Corollary 4.7's finite local extension convention along the actual invariant outward bundle. -/
theorem SetValuedSystem.invariant_outwardNormalBundle_regular_sphere_extensions
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (M : Set E) (hM : M ⊆ system.domain) (hcompact : IsCompact M)
    (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hvisible : system.SourceVisible M)
    (hinvariant : setValuedImage system.map system.radius M = M)
    (hr : 2 ≤ r) (hs : 2 ≤ s)
    (p : E × E) (hp : p ∈ outwardNormalBundle M hregular boundary) :
    ∃ extension : LocalExtensionAt (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ inverseExtension : LocalExtensionAt (min r s - 1) (range system.boundaryFormula)
          (system.boundaryInverseOnAmbient hcontraction) p,
        (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
        (∀ q ∈ inverseExtension.neighborhood, ‖(inverseExtension.extension q).2‖ = 1) ∧
        ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
            bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
          ∀ v : bundleTangentSpace p.2,
            (differential v : E × E) = fderiv ℝ extension.extension p v := by
  apply system.exists_regular_sphere_boundaryExtensions_on_invariant hcontraction
    (outwardNormalBundle M hregular boundary) _
    (system.image_outwardNormalBundle_of_invariant hcontraction M hM hcompact
      hregular boundary hvisible hinvariant) hr hs p hp
  intro q hq
  have h := outwardNormalBundle_subset M hregular boundary hq
  exact ⟨hM (hregular.isClosed.frontier_subset h.1), h.2⟩

/-- The smooth counterpart has the same actual forward and inverse formulas,
fixed sphere-valued neighborhoods, and nonsingular full-bundle differential. -/
theorem SetValuedSystem.invariant_outwardNormalBundle_smooth_sphere_extensions
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse)
    (M : Set E) (hM : M ⊆ system.domain) (hcompact : IsCompact M)
    (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hvisible : system.SourceVisible M)
    (hinvariant : setValuedImage system.map system.radius M = M)
    (p : E × E) (hp : p ∈ outwardNormalBundle M hregular boundary) :
    ∃ extension : SmoothLocalExtensionAt (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ inverseExtension : SmoothLocalExtensionAt (range system.boundaryFormula)
          (system.boundaryInverseOnAmbient hcontraction) p,
        (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
        (∀ q ∈ inverseExtension.neighborhood, ‖(inverseExtension.extension q).2‖ = 1) ∧
        ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
            bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
          ∀ v : bundleTangentSpace p.2,
            (differential v : E × E) = fderiv ℝ extension.extension p v := by
  apply system.exists_smooth_sphere_boundaryExtensions_on_invariant hcontraction hmap hradius hinverse
    (outwardNormalBundle M hregular boundary) _
    (system.image_outwardNormalBundle_of_invariant hcontraction M hM hcompact
      hregular boundary hvisible hinvariant) p hp
  intro q hq
  have h := outwardNormalBundle_subset M hregular boundary hq
  exact ⟨hM (hregular.isClosed.frontier_subset h.1), h.2⟩

end BoundedUncertainty
