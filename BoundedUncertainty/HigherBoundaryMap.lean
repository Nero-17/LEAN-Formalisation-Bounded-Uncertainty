import BoundedUncertainty.HigherLinearLift
import BoundedUncertainty.ContractionCharacterization

/-!
# Higher regularity of the boundary formula

The ambient representative is the actual linear formula followed by the actual
exponential formula. Its restriction agrees with both the contraction-free
candidate and, under contraction, the typed boundary map. This file proves
forward local regularity, not higher regularity of the inverse.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- A total ambient representative of the contraction-free candidate boundary
formula. Its values outside the source bundle are not constrained. -/
noncomputable def SetValuedSystem.boundaryFormulaOnAmbient
    (system : SetValuedSystem (E := E) r s) : E × E → E × E :=
  exponentialMap system.radius system.radiusGradientOnAmbient ∘ system.linearLiftOnAmbient

/-- The ambient representative agrees with the actual candidate on every
domain point and unit normal. -/
theorem SetValuedSystem.boundaryFormulaOnAmbient_apply
    (system : SetValuedSystem (E := E) r s)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    system.boundaryFormulaOnAmbient ((p.1 : E), (p.2 : E)) = system.boundaryFormula p := by
  simp only [SetValuedSystem.boundaryFormulaOnAmbient, Function.comp_apply,
    system.linearLiftOnAmbient_apply, SetValuedSystem.boundaryFormula]

/-- Under contraction this is also the ambient coordinate expression of beta. -/
theorem SetValuedSystem.boundaryFormulaOnAmbient_eq_boundaryMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    system.boundaryFormulaOnAmbient ((p.1 : E), (p.2 : E)) =
      (((system.boundaryMap hcontraction p).1 : E),
        ((system.boundaryMap hcontraction p).2 : E)) :=
  (system.boundaryFormulaOnAmbient_apply p).trans
    (system.boundaryFormula_eq_boundaryMap hcontraction p)

/-- The forward higher-regularity assertion of Theorem 3.14, expressed using
the manuscript's local ambient extension convention on the actual source bundle. -/
theorem SetValuedSystem.hasLocalExtensionOn_boundaryFormulaOnAmbient
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    HasLocalExtensionOn (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
      system.boundaryFormulaOnAmbient :=
  HasLocalExtensionOn.comp
    ((system.hasLocalExtensionOn_exponentialMap hcontraction).of_le
      (Nat.sub_le_sub_right (Nat.min_le_left r s) 1))
    (system.hasLocalExtensionOn_linearLiftOnAmbient.of_le
      (Nat.sub_le_sub_right (Nat.min_le_right r s) 1))
    system.linearLiftOnAmbient_mapsTo

end BoundedUncertainty
