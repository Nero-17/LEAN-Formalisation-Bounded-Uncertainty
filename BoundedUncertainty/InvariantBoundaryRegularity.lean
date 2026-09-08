import BoundedUncertainty.ForwardNormalBundle

/-! Regularity of the actual boundary map restricted to an invariant normal bundle. -/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {r s : ℕ}

/-- The ambient inverse is a left inverse on every genuine state and unit-normal pair. -/
theorem SetValuedSystem.boundaryInverseOnAmbient_leftInvOn
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    LeftInvOn (system.boundaryInverseOnAmbient hcontraction) system.boundaryFormulaOnAmbient
      (system.domain ×ˢ {n : E | ‖n‖ = 1}) := by
  intro p hp
  rw [system.boundaryFormulaOnAmbient_apply (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)]
  exact system.boundaryInverseOnAmbient_formula hcontraction (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)

/-- Any invariant subset of the state bundle lies in the actual range of beta. -/
theorem SetValuedSystem.invariant_subset_range_boundaryFormula
    (system : SetValuedSystem (E := E) r s) (B : Set (E × E))
    (hB : B ⊆ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (hinvariant : system.boundaryFormulaOnAmbient '' B = B) :
    B ⊆ range system.boundaryFormula := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hinvariant.symm ▸ hp
  exact ⟨(⟨q.1, (hB hq).1⟩, ⟨q.2, (hB hq).2⟩),
    (system.boundaryFormulaOnAmbient_apply
      (⟨q.1, (hB hq).1⟩, ⟨q.2, (hB hq).2⟩)).symm⟩

theorem SetValuedSystem.boundaryInverseOnAmbient_mapsTo_invariant
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set (E × E)) (hB : B ⊆ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (hinvariant : system.boundaryFormulaOnAmbient '' B = B) :
    MapsTo (system.boundaryInverseOnAmbient hcontraction) B B := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hinvariant.symm ▸ hp
  rw [system.boundaryInverseOnAmbient_leftInvOn hcontraction (hB hq)]
  exact hq

/-- The restriction is a homeomorphism, with the same actual forward and inverse formulas. -/
noncomputable def SetValuedSystem.boundaryHomeomorphInvariant
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set (E × E)) (hB : B ⊆ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (hinvariant : system.boundaryFormulaOnAmbient '' B = B) : B ≃ₜ B where
  toFun p := ⟨system.boundaryFormulaOnAmbient p,
    hinvariant.subset (mem_image_of_mem _ p.property)⟩
  invFun p := ⟨system.boundaryInverseOnAmbient hcontraction p,
    system.boundaryInverseOnAmbient_mapsTo_invariant hcontraction B hB hinvariant p.property⟩
  left_inv p := Subtype.ext (system.boundaryInverseOnAmbient_leftInvOn hcontraction (hB p.property))
  right_inv p := Subtype.ext (system.boundaryFormulaOnAmbient_inverse hcontraction p
    (system.invariant_subset_range_boundaryFormula B hB hinvariant p.property))
  continuous_toFun :=
    (continuousOn_iff_continuous_restrict.mp
      ((system.hasLocalExtensionOn_boundaryFormulaOnAmbient hcontraction).continuousOn.mono hB)).subtype_mk _
  continuous_invFun :=
    (continuousOn_iff_continuous_restrict.mp
      ((system.hasLocalExtensionOn_boundaryInverseOnAmbient hcontraction).continuousOn.mono
        (system.invariant_subset_range_boundaryFormula B hB hinvariant))).subtype_mk _

theorem SetValuedSystem.boundaryHomeomorphInvariant_apply
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set (E × E)) (hB : B ⊆ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (hinvariant : system.boundaryFormulaOnAmbient '' B = B) (p : B) :
    ((system.boundaryHomeomorphInvariant hcontraction B hB hinvariant p) : E × E) =
      system.boundaryFormulaOnAmbient p := rfl

theorem SetValuedSystem.boundaryHomeomorphInvariant_symm_apply
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set (E × E)) (hB : B ⊆ system.domain ×ˢ {n : E | ‖n‖ = 1})
    (hinvariant : system.boundaryFormulaOnAmbient '' B = B) (p : B) :
    (((system.boundaryHomeomorphInvariant hcontraction B hB hinvariant).symm p) : E × E) =
      system.boundaryInverseOnAmbient hcontraction p := rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Corollary 4.7 in the manuscript's ambient-extension convention.
The bundle itself is not asserted to be a C^(k-1) embedded manifold. -/
theorem SetValuedSystem.invariant_outwardNormalBundle_regular_homeomorphism
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (M : Set E) (hM : M ⊆ system.domain) (hcompact : IsCompact M)
    (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hvisible : system.SourceVisible M)
    (hinvariant : setValuedImage system.map system.radius M = M) :
    (∃ equivalence : outwardNormalBundle M hregular boundary ≃ₜ outwardNormalBundle M hregular boundary,
      (∀ p, (equivalence p : E × E) = system.boundaryFormulaOnAmbient p) ∧
      (∀ p, (equivalence.symm p : E × E) = system.boundaryInverseOnAmbient hcontraction p)) ∧
    HasLocalExtensionOn (min r s - 1) (outwardNormalBundle M hregular boundary)
      system.boundaryFormulaOnAmbient ∧
    HasLocalExtensionOn (min r s - 1) (outwardNormalBundle M hregular boundary)
      (system.boundaryInverseOnAmbient hcontraction) := by
  have hbundle : outwardNormalBundle M hregular boundary ⊆
      system.domain ×ˢ {n : E | ‖n‖ = 1} := by
    intro p hp
    have h := outwardNormalBundle_subset M hregular boundary hp
    exact ⟨hM (hregular.isClosed.frontier_subset h.1), h.2⟩
  have himage := system.image_outwardNormalBundle_of_invariant hcontraction M hM hcompact
    hregular boundary hvisible hinvariant
  exact ⟨⟨system.boundaryHomeomorphInvariant hcontraction _ hbundle himage,
      fun _ => rfl, fun _ => rfl⟩,
    (system.hasLocalExtensionOn_boundaryFormulaOnAmbient hcontraction).mono_domain hbundle,
    (system.hasLocalExtensionOn_boundaryInverseOnAmbient hcontraction).mono_domain
      (system.invariant_subset_range_boundaryFormula _ hbundle himage)⟩

end BoundedUncertainty
