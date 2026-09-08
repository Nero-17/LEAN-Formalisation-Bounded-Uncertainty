import BoundedUncertainty.HigherBoundaryMap
import BoundedUncertainty.HigherLinearInverse
import BoundedUncertainty.BoundaryHomeomorph

/-!
The continuous inverse of the genuine boundary formula on its actual ambient
range. The zero value outside that range is only a total representative; no
regularity is asserted there. The intermediate inverse recovers the true
linear-lift output and therefore lies over the possibly nonclosed image f(X).
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

theorem SetValuedSystem.isEmbedding_boundaryFormula
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    IsEmbedding system.boundaryFormula := by
  have hforget : IsEmbedding (fun p : system.domain × {n : E // ‖n‖ = 1} =>
      ((p.1 : E), (p.2 : E))) :=
    IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal
  have heq : system.boundaryFormula = (fun p : system.domain × {n : E // ‖n‖ = 1} =>
      ((p.1 : E), (p.2 : E))) ∘ system.boundaryMap hcontraction := by
    funext p
    exact system.boundaryFormula_eq_boundaryMap hcontraction p
  rw [heq]
  exact hforget.comp (system.isEmbedding_boundaryMap hcontraction)

/-- The existing topological embedding expressed in ambient output coordinates. -/
noncomputable def SetValuedSystem.boundaryAmbientHomeomorphRange
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    (system.domain × {n : E // ‖n‖ = 1}) ≃ₜ Set.range system.boundaryFormula :=
  (system.isEmbedding_boundaryFormula hcontraction).toHomeomorph

/-- An ambient representative of the actual inverse of beta. -/
noncomputable def SetValuedSystem.boundaryInverseOnAmbient
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : E × E) : E × E := by
  classical
  exact if hp : p ∈ Set.range system.boundaryFormula then
    (((system.boundaryAmbientHomeomorphRange hcontraction).symm ⟨p, hp⟩).1,
      ((system.boundaryAmbientHomeomorphRange hcontraction).symm ⟨p, hp⟩).2) else (0, 0)

theorem SetValuedSystem.boundaryInverseOnAmbient_apply
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : Set.range system.boundaryFormula) :
    system.boundaryInverseOnAmbient hcontraction p =
      ((((system.boundaryAmbientHomeomorphRange hcontraction).symm p).1 : E),
        (((system.boundaryAmbientHomeomorphRange hcontraction).symm p).2 : E)) := by
  simp only [SetValuedSystem.boundaryInverseOnAmbient, dif_pos p.property]

theorem SetValuedSystem.continuousOn_boundaryInverseOnAmbient
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    ContinuousOn (system.boundaryInverseOnAmbient hcontraction)
      (Set.range system.boundaryFormula) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.range system.boundaryFormula).restrict
      (system.boundaryInverseOnAmbient hcontraction) = fun p =>
        ((((system.boundaryAmbientHomeomorphRange hcontraction).symm p).1 : E),
          (((system.boundaryAmbientHomeomorphRange hcontraction).symm p).2 : E)) := by
    funext p
    exact system.boundaryInverseOnAmbient_apply hcontraction p
  rw [heq]
  exact (continuous_subtype_val.comp
    (continuous_fst.comp (system.boundaryAmbientHomeomorphRange hcontraction).symm.continuous)).prodMk
      (continuous_subtype_val.comp
        (continuous_snd.comp (system.boundaryAmbientHomeomorphRange hcontraction).symm.continuous))

theorem SetValuedSystem.boundaryInverseOnAmbient_mapsTo
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    MapsTo (system.boundaryInverseOnAmbient hcontraction) (Set.range system.boundaryFormula)
      (system.domain ×ˢ {n : E | ‖n‖ = 1}) := by
  intro p hp
  rw [system.boundaryInverseOnAmbient_apply hcontraction ⟨p, hp⟩]
  exact ⟨((system.boundaryAmbientHomeomorphRange hcontraction).symm ⟨p, hp⟩).1.property,
    ((system.boundaryAmbientHomeomorphRange hcontraction).symm ⟨p, hp⟩).2.property⟩

theorem SetValuedSystem.boundaryFormulaOnAmbient_inverse
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : E × E) (hp : p ∈ Set.range system.boundaryFormula) :
    system.boundaryFormulaOnAmbient (system.boundaryInverseOnAmbient hcontraction p) = p := by
  rw [system.boundaryInverseOnAmbient_apply hcontraction ⟨p, hp⟩,
    system.boundaryFormulaOnAmbient_apply]
  exact congrArg Subtype.val
    ((system.boundaryAmbientHomeomorphRange hcontraction).apply_symm_apply ⟨p, hp⟩)

theorem SetValuedSystem.boundaryInverseOnAmbient_formula
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    system.boundaryInverseOnAmbient hcontraction (system.boundaryFormula p) =
      ((p.1 : E), (p.2 : E)) := by
  rw [system.boundaryInverseOnAmbient_apply hcontraction ⟨system.boundaryFormula p, ⟨p, rfl⟩⟩]
  have hinverse := (system.boundaryAmbientHomeomorphRange hcontraction).symm_apply_apply p
  change (system.boundaryAmbientHomeomorphRange hcontraction).symm
    ⟨system.boundaryFormula p, ⟨p, rfl⟩⟩ = p at hinverse
  rw [hinverse]

theorem SetValuedSystem.linearLiftInverseOnAmbient_linearLiftOnAmbient
    (system : SetValuedSystem (E := E) r s)
    (p : E × E) (hp : p ∈ system.domain ×ˢ {n : E | ‖n‖ = 1}) :
    system.linearLiftInverseOnAmbient (system.linearLiftOnAmbient p) = p := by
  rw [system.linearLiftOnAmbient_apply (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)]
  change system.linearLiftInverseOnAmbient
    (((system.linearLiftHomeomorph (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)).1 : E),
      ((system.linearLiftHomeomorph (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)).2 : E)) = p
  rw [system.linearLiftInverseOnAmbient_apply,
    system.linearLiftHomeomorph.symm_apply_apply]

/-- The intermediate recovered centre belongs to the actual deterministic image. -/
theorem SetValuedSystem.linearLiftOnAmbient_mapsTo_image
    (system : SetValuedSystem (E := E) r s) :
    MapsTo system.linearLiftOnAmbient (system.domain ×ˢ {n : E | ‖n‖ = 1})
      ((system.map '' system.domain) ×ˢ {n : E | ‖n‖ = 1}) := by
  intro p hp
  rw [system.linearLiftOnAmbient_apply (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)]
  exact ⟨system.linearLift_position_mem_image (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩),
    (system.linearLift (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)).2.property⟩

end BoundedUncertainty
