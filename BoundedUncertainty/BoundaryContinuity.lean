import BoundedUncertainty.BoundaryMap
import BoundedUncertainty.VaryingLinearLift

/-!
The continuous part of Theorem 3.14, and the injectivity/range of its linear lift.
Global injectivity and inverse continuity of the full exponential/boundary map
are not asserted here.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.continuous_derivativeEquiv
    (system : SetValuedSystem (E := E) r s) :
    Continuous (fun x : system.domain => (system.derivativeEquiv x : E →L[ℝ] E)) := by
  have heq : (fun x : system.domain => (system.derivativeEquiv x : E →L[ℝ] E)) =
      system.diffeomorphism.forward_extension.ambientDerivative := by
    funext x
    exact system.derivativeEquiv_eq_ambientDerivative x
  rw [heq]
  exact system.diffeomorphism.forward_extension.continuous_ambientDerivative
    system.regular_closed system.map_order_pos

/-- Continuity includes the varying inverse transpose at the source point. -/
theorem SetValuedSystem.continuous_linearLift
    (system : SetValuedSystem (E := E) r s) :
    Continuous system.linearLift := by
  have hposition : Continuous (fun p : system.domain × {n : E // ‖n‖ = 1} =>
      system.map (p.1 : E)) :=
    system.diffeomorphism.forward_extension.continuousOn.restrict.comp continuous_fst
  exact (hposition.subtype_mk _).prodMk
    (continuous_normalizedInverseTransposeHomeomorph_family
      system.derivativeEquiv system.continuous_derivativeEquiv)

theorem SetValuedSystem.continuous_boundaryMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    Continuous (system.boundaryMap hcontraction) := by
  have hcompose := (system.continuous_exponentialLift hcontraction).comp
    system.continuous_linearLift
  exact (hcompose.fst.subtype_mk _).prodMk hcompose.snd

/-- The linear lift alone is injective; this does not assert injectivity of beta. -/
theorem SetValuedSystem.linearLift_injective
    (system : SetValuedSystem (E := E) r s) :
    Function.Injective system.linearLift := by
  intro p q hpq
  have hx : p.1 = q.1 := Subtype.ext
    (system.diffeomorphism.injectiveOn p.1.property q.1.property
      (congrArg (fun v : system.domain × {n : E // ‖n‖ = 1} => (v.1 : E)) hpq))
  apply Prod.ext hx
  have hn := congrArg Prod.snd hpq
  change normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv p.1)) p.2 =
    normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv q.1)) q.2 at hn
  rw [hx] at hn
  exact (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv q.1))).injective hn

/-- The range of the linear lift is exactly f(X) times the unit sphere. -/
theorem SetValuedSystem.range_linearLift
    (system : SetValuedSystem (E := E) r s) :
    Set.range system.linearLift =
      {p : system.domain × {n : E // ‖n‖ = 1} | (p.1 : E) ∈ system.map '' system.domain} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact system.linearLift_position_mem_image q
  · rintro ⟨x, hx, hfx⟩
    refine ⟨(⟨x, hx⟩, (normalizedLinearHomeomorph
      (inverseTranspose (system.derivativeEquiv ⟨x, hx⟩))).symm p.2), ?_⟩
    apply Prod.ext
    · exact Subtype.ext hfx
    · exact (normalizedLinearHomeomorph
        (inverseTranspose (system.derivativeEquiv ⟨x, hx⟩))).apply_symm_apply p.2

end BoundedUncertainty
