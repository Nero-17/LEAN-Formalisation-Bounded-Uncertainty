import BoundedUncertainty.BoundaryInverseRepresentation
import BoundedUncertainty.HigherExponentialInverse

/-!
The inverse of beta has the same finite local ambient regularity as the
forward map. The continuous inverse is first passed through L, giving a
continuous right inverse of E on beta's actual range. The scalar implicit
function theorem upgrades this intermediate inverse to C^(r-1). Composition
with the actual inverse of L gives C^(min(r,s)-1), without closing f(X).
-/

namespace BoundedUncertainty

open Set Topology

section LocalExtensions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local extensions depend only on values on their specified domain. -/
theorem HasLocalExtensionOn.congr {order : ℕ} {X : Set E} {f g : E → F}
    (h : HasLocalExtensionOn order X f) (heq : EqOn f g X) :
    HasLocalExtensionOn order X g := by
  intro x hx
  obtain ⟨extension⟩ := h x hx
  exact ⟨{
    neighborhood := extension.neighborhood
    isOpen_neighborhood := extension.isOpen_neighborhood
    mem_neighborhood := extension.mem_neighborhood
    extension := extension.extension
    contDiffOn_extension := extension.contDiffOn_extension
    agrees := fun y hy => (extension.agrees hy).trans (heq hy.1)
  }⟩

end LocalExtensions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- Theorem 3.14: the genuine beta inverse has local ambient regularity
`C^(min(r,s)-1)` on its actual image. -/
theorem SetValuedSystem.hasLocalExtensionOn_boundaryInverseOnAmbient
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    HasLocalExtensionOn (min r s - 1) (Set.range system.boundaryFormula)
      (system.boundaryInverseOnAmbient hcontraction) := by
  have hintermediate := system.hasLocalExtensionOn_exponentialInverse_of_continuous hcontraction
    (system.linearLiftOnAmbient ∘ system.boundaryInverseOnAmbient hcontraction)
    (Set.range system.boundaryFormula)
    (system.hasLocalExtensionOn_linearLiftOnAmbient.continuousOn.comp
      (system.continuousOn_boundaryInverseOnAmbient hcontraction)
      (system.boundaryInverseOnAmbient_mapsTo hcontraction))
    (system.linearLiftOnAmbient_mapsTo.comp (system.boundaryInverseOnAmbient_mapsTo hcontraction))
    (system.boundaryFormulaOnAmbient_inverse hcontraction)
  have hcomposed := HasLocalExtensionOn.comp
    (system.hasLocalExtensionOn_linearLiftInverseOnAmbient.of_le
      (Nat.sub_le_sub_right (Nat.min_le_right r s) 1))
    (hintermediate.of_le (Nat.sub_le_sub_right (Nat.min_le_left r s) 1))
    (system.linearLiftOnAmbient_mapsTo_image.comp
      (system.boundaryInverseOnAmbient_mapsTo hcontraction))
  apply hcomposed.congr
  intro p hp
  exact system.linearLiftInverseOnAmbient_linearLiftOnAmbient _
    (system.boundaryInverseOnAmbient_mapsTo hcontraction hp)

/-- Both directions of Theorem 3.14, with the established topological embedding
and the manuscript's local ambient extension convention stated together. -/
theorem SetValuedSystem.boundaryFormula_regular_homeomorphism
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    IsEmbedding system.boundaryFormula ∧
      HasLocalExtensionOn (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient ∧
      HasLocalExtensionOn (min r s - 1) (Set.range system.boundaryFormula)
        (system.boundaryInverseOnAmbient hcontraction) :=
  ⟨system.isEmbedding_boundaryFormula hcontraction,
    system.hasLocalExtensionOn_boundaryFormulaOnAmbient hcontraction,
    system.hasLocalExtensionOn_boundaryInverseOnAmbient hcontraction⟩

/-- In the full-image case the actual ambient range is the entire state bundle. -/
theorem SetValuedSystem.range_boundaryFormula_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain) :
    Set.range system.boundaryFormula = system.domain ×ˢ {n : E | ‖n‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    rw [system.boundaryFormula_eq_boundaryMap hcontraction q]
    exact ⟨(system.boundaryMap hcontraction q).1.property,
      (system.boundaryMap hcontraction q).2.property⟩
  · intro hp
    obtain ⟨q, hq⟩ := system.boundaryMap_surjective_of_image_eq_domain hcontraction himage
      (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)
    refine ⟨q, ?_⟩
    rw [system.boundaryFormula_eq_boundaryMap hcontraction q, hq]

theorem SetValuedSystem.hasLocalExtensionOn_boundaryInverseOnAmbient_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain) :
    HasLocalExtensionOn (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
      (system.boundaryInverseOnAmbient hcontraction) := by
  rw [← system.range_boundaryFormula_of_image_eq_domain hcontraction himage]
  exact system.hasLocalExtensionOn_boundaryInverseOnAmbient hcontraction

end BoundedUncertainty
