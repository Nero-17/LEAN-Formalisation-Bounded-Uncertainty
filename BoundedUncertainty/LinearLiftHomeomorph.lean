import BoundedUncertainty.BoundaryContinuity

/-!
# The linear lift as a homeomorphism onto its image bundle

The deterministic map is a homeomorphism from its domain onto its actual image.
The normalized inverse-transpose lift has the same property on the unit-normal
bundles. Its inverse uses the normalized transpose of the derivative at the
recovered source point. No closedness of the deterministic image is assumed.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- The deterministic map, with its actual image as codomain. Its inverse is
continuous in the subspace topology by the given local inverse extensions. -/
noncomputable def SetValuedSystem.mapImageHomeomorph
    (system : SetValuedSystem (E := E) r s) :
    system.domain ≃ₜ (system.map '' system.domain) where
  toFun x := ⟨system.map x, ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨system.diffeomorphism.inverse y,
    system.diffeomorphism.inverse_mapsTo y.property⟩
  left_inv x := Subtype.ext (system.diffeomorphism.left_inverse x.property)
  right_inv y := Subtype.ext (system.diffeomorphism.right_inverse y.property)
  continuous_toFun := system.diffeomorphism.forward_extension.continuousOn.restrict.subtype_mk _
  continuous_invFun := system.diffeomorphism.inverse_extension.continuousOn.restrict.subtype_mk _

/-- The inverses of the normalized inverse-transpose maps vary jointly
continuously with the source point and the outgoing unit normal. -/
theorem SetValuedSystem.continuous_inverseLinearNormal
    (system : SetValuedSystem (E := E) r s) :
    Continuous (fun p : system.domain × {n : E // ‖n‖ = 1} =>
      (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv p.1))).symm p.2) := by
  change Continuous (fun p : system.domain × {n : E // ‖n‖ = 1} =>
    normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv p.1)).symm p.2)
  exact continuous_normalizedLinearHomeomorph_family
    (fun x => (inverseTranspose (system.derivativeEquiv x)).symm)
    (continuous_linearEquiv_symm (fun x => inverseTranspose (system.derivativeEquiv x))
      (continuous_inverseTranspose system.derivativeEquiv system.continuous_derivativeEquiv))

/-- Definition 3.11's linear lift is a homeomorphism onto `f(X) × S`.
Neither contraction nor closedness of `f(X)` is needed for this linear step. -/
noncomputable def SetValuedSystem.linearLiftHomeomorph
    (system : SetValuedSystem (E := E) r s) :
    (system.domain × {n : E // ‖n‖ = 1}) ≃ₜ
      ((system.map '' system.domain) × {n : E // ‖n‖ = 1}) where
  toFun p := (system.mapImageHomeomorph p.1,
    normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv p.1)) p.2)
  invFun p := (system.mapImageHomeomorph.symm p.1,
    (normalizedLinearHomeomorph
      (inverseTranspose (system.derivativeEquiv (system.mapImageHomeomorph.symm p.1)))).symm p.2)
  left_inv p := by
    apply Prod.ext
    · exact system.mapImageHomeomorph.symm_apply_apply p.1
    · simp only [Homeomorph.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · exact system.mapImageHomeomorph.apply_symm_apply p.1
    · exact (normalizedLinearHomeomorph
        (inverseTranspose (system.derivativeEquiv (system.mapImageHomeomorph.symm p.1)))).apply_symm_apply p.2
  continuous_toFun :=
    (system.mapImageHomeomorph.continuous.comp continuous_fst).prodMk
      (continuous_normalizedInverseTransposeHomeomorph_family
        system.derivativeEquiv system.continuous_derivativeEquiv)
  continuous_invFun := by
    have hsource : Continuous
        (fun p : (system.map '' system.domain) × {n : E // ‖n‖ = 1} =>
          system.mapImageHomeomorph.symm p.1) :=
      system.mapImageHomeomorph.symm.continuous.comp continuous_fst
    have hnormal : Continuous
        (fun p : (system.map '' system.domain) × {n : E // ‖n‖ = 1} =>
          (normalizedLinearHomeomorph
            (inverseTranspose (system.derivativeEquiv
              (system.mapImageHomeomorph.symm p.1)))).symm p.2) :=
      Continuous.comp
        (f := fun p : (system.map '' system.domain) × {n : E // ‖n‖ = 1} =>
          (system.mapImageHomeomorph.symm p.1, p.2))
        (g := fun p : system.domain × {n : E // ‖n‖ = 1} =>
          (normalizedLinearHomeomorph
            (inverseTranspose (system.derivativeEquiv p.1))).symm p.2)
        system.continuous_inverseLinearNormal (hsource.prodMk continuous_snd)
    exact hsource.prodMk hnormal

/-- Forgetting the refined image codomain recovers the previously defined lift. -/
theorem SetValuedSystem.linearLiftHomeomorph_coe_apply
    (system : SetValuedSystem (E := E) r s)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    (((system.linearLiftHomeomorph p).1 : E), (system.linearLiftHomeomorph p).2) =
      (((system.linearLift p).1 : E), (system.linearLift p).2) :=
  rfl

/-- The inverse position is the given deterministic inverse. -/
@[simp] theorem SetValuedSystem.linearLiftHomeomorph_symm_position
    (system : SetValuedSystem (E := E) r s)
    (p : (system.map '' system.domain) × {n : E // ‖n‖ = 1}) :
    ((system.linearLiftHomeomorph.symm p).1 : E) = system.diffeomorphism.inverse p.1 :=
  rfl

/-- The inverse normal is the normalized transpose of the source differential,
evaluated at the recovered source point. -/
theorem SetValuedSystem.linearLiftHomeomorph_symm_normal
    (system : SetValuedSystem (E := E) r s)
    (p : (system.map '' system.domain) × {n : E // ‖n‖ = 1}) :
    ((system.linearLiftHomeomorph.symm p).2 : E) =
      ‖ContinuousLinearMap.adjoint
        (system.derivativeEquiv (system.mapImageHomeomorph.symm p.1)).toContinuousLinearMap
          (p.2 : E)‖⁻¹ •
      ContinuousLinearMap.adjoint
        (system.derivativeEquiv (system.mapImageHomeomorph.symm p.1)).toContinuousLinearMap
          (p.2 : E) :=
  rfl

end BoundedUncertainty
