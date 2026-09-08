import BoundedUncertainty.BoundaryInjectivity
import BoundedUncertainty.SelfSurjectivity
import BoundedUncertainty.ContractionNecessity

/-!
Theorem 3.17: the candidate formula defines a bijection exactly under contraction.
The candidate is constructed before any contraction assumption. Its codomain is
the ambient product, and the bijection predicate explicitly requires the output
to belong to the domain and unit sphere.
-/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- The boundary formula before assuming that its output normal is a unit vector. -/
noncomputable def SetValuedSystem.boundaryFormula
    (system : SetValuedSystem (E := E) r s)
    (p : system.domain × {n : E // ‖n‖ = 1}) : E × E :=
  exponentialMap system.radius system.radiusGradientOnAmbient
    (((system.linearLift p).1 : E), ((system.linearLift p).2 : E))

/-- Well-definedness, injectivity and surjectivity of the candidate formula. -/
def SetValuedSystem.BoundaryFormulaIsBijection
    (system : SetValuedSystem (E := E) r s) : Prop :=
  Set.BijOn system.boundaryFormula Set.univ
    (system.domain ×ˢ {n : E | ‖n‖ = 1})

theorem SetValuedSystem.boundaryFormula_eq_boundaryMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    system.boundaryFormula p =
      (((system.boundaryMap hcontraction p).1 : E),
        ((system.boundaryMap hcontraction p).2 : E)) := rfl

theorem SetValuedSystem.boundaryFormulaIsBijection_of_isContraction
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain) :
    system.BoundaryFormulaIsBijection := by
  refine ⟨?_, ?_, ?_⟩
  · intro p _
    rw [system.boundaryFormula_eq_boundaryMap hcontraction p]
    exact ⟨(system.boundaryMap hcontraction p).1.property,
      (system.boundaryMap hcontraction p).2.property⟩
  · intro p _ q _ hpq
    apply system.boundaryMap_injective hcontraction
    rw [system.boundaryFormula_eq_boundaryMap hcontraction p,
      system.boundaryFormula_eq_boundaryMap hcontraction q] at hpq
    exact Prod.ext (Subtype.ext (congrArg (fun t : E × E => t.1) hpq))
      (Subtype.ext (congrArg (fun t : E × E => t.2) hpq))
  · rintro ⟨z, u⟩ ⟨hz, hu⟩
    obtain ⟨p, hp⟩ := system.boundaryMap_surjective_of_image_eq_domain hcontraction himage
      (⟨z, hz⟩, ⟨u, hu⟩)
    refine ⟨p, mem_univ _, ?_⟩
    rw [system.boundaryFormula_eq_boundaryMap hcontraction p, hp]

theorem SetValuedSystem.isContraction_of_boundaryFormulaIsBijection
    (system : SetValuedSystem (E := E) r s)
    (himage : system.map '' system.domain = system.domain)
    (hbijective : system.BoundaryFormulaIsBijection) : system.IsContraction := by
  apply system.isContraction_of_exponentialMap_injOn
  rintro ⟨y₁, n₁⟩ ⟨hy₁, hn₁⟩ ⟨y₂, n₂⟩ ⟨hy₂, hn₂⟩ heq
  obtain ⟨p, hp⟩ := system.linearLift_surjective_of_image_eq_domain himage
    (⟨y₁, hy₁⟩, ⟨n₁, hn₁⟩)
  obtain ⟨q, hq⟩ := system.linearLift_surjective_of_image_eq_domain himage
    (⟨y₂, hy₂⟩, ⟨n₂, hn₂⟩)
  have hpq : p = q := by
    apply hbijective.injOn (mem_univ p) (mem_univ q)
    simpa only [SetValuedSystem.boundaryFormula, hp, hq] using heq
  have hlifts : system.linearLift p = system.linearLift q := congrArg system.linearLift hpq
  rw [hp, hq] at hlifts
  exact Prod.ext
    (congrArg (fun t : system.domain × {n : E // ‖n‖ = 1} => (t.1 : E)) hlifts)
    (congrArg (fun t : system.domain × {n : E // ‖n‖ = 1} => (t.2 : E)) hlifts)

/-- Theorem 3.17 with no contraction hypothesis built into the candidate formula. -/
theorem SetValuedSystem.isContraction_iff_boundaryFormulaIsBijection
    (system : SetValuedSystem (E := E) r s)
    (himage : system.map '' system.domain = system.domain) :
    system.IsContraction ↔ system.BoundaryFormulaIsBijection :=
  ⟨fun hcontraction => system.boundaryFormulaIsBijection_of_isContraction hcontraction himage,
    system.isContraction_of_boundaryFormulaIsBijection himage⟩

end BoundedUncertainty
