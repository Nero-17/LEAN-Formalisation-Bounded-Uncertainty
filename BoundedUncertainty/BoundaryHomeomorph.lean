import BoundedUncertainty.ExponentialEmbedding
import BoundedUncertainty.LinearLiftHomeomorph
import BoundedUncertainty.SelfSurjectivity
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The boundary map as a homeomorphism onto its actual range

This proves Theorem 3.14's topological conclusion for the genuine boundary-map
formula. The exponential lift embeds the closed set of admissible centres;
restriction gives an embedding on `f(X)`, even when that image is not closed.
Composition with the linear-lift homeomorphism then gives the result for beta.
No full-image assumption or positive lower bound on the radius is imposed.
-/

namespace BoundedUncertainty

open Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- Every subset of the admissible centres inherits the exponential embedding. -/
theorem SetValuedSystem.isEmbedding_restrictedExponentialLift_of_admissible
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (centres : Set E) (hcentres : centres ⊆ system.admissibleCentres) :
    IsEmbedding (system.restrictedExponentialLift hcontraction centres
      (hcentres.trans system.admissibleCentres_subset)) := by
  have hclosed := system.isClosedEmbedding_restrictedExponentialLift hcontraction
    system.admissibleCentres system.isClosed_admissibleCentres
    system.admissibleCentres_subset system.admissibleCentres_ball_subset
  exact hclosed.isEmbedding.comp
    ((IsEmbedding.inclusion hcentres).prodMap IsEmbedding.id)

/-- The actual image `f(X)` need not be closed. -/
theorem SetValuedSystem.isEmbedding_exponentialLift_on_image
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    IsEmbedding (system.restrictedExponentialLift hcontraction (system.map '' system.domain)
      (system.image_subset_admissibleCentres.trans system.admissibleCentres_subset)) :=
  system.isEmbedding_restrictedExponentialLift_of_admissible hcontraction
    (system.map '' system.domain) system.image_subset_admissibleCentres

/-- Theorem 3.14: beta is a topological embedding under pointwise contraction. -/
theorem SetValuedSystem.isEmbedding_boundaryMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    IsEmbedding (system.boundaryMap hcontraction) := by
  have hcompose := (system.isEmbedding_exponentialLift_on_image hcontraction).comp
    system.linearLiftHomeomorph.isEmbedding
  have hforget : Continuous (fun p : system.domain × {n : E // ‖n‖ = 1} =>
      ((p.1 : E), p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact IsEmbedding.of_comp (system.continuous_boundaryMap hcontraction) hforget hcompose

/-- Theorem 3.14's homeomorphism onto the actual range of beta. -/
noncomputable def SetValuedSystem.betaHomeomorphRange
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    (system.domain × {n : E // ‖n‖ = 1}) ≃ₜ
      Set.range (system.boundaryMap hcontraction) :=
  (system.isEmbedding_boundaryMap hcontraction).toHomeomorph

@[simp]
theorem SetValuedSystem.betaHomeomorphRange_apply
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    (system.betaHomeomorphRange hcontraction p).val = system.boundaryMap hcontraction p :=
  rfl

/-- The inverse is continuous in the subspace topology on beta's actual range. -/
theorem SetValuedSystem.continuous_betaHomeomorphRange_symm
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    Continuous (system.betaHomeomorphRange hcontraction).symm :=
  (system.betaHomeomorphRange hcontraction).symm.continuous

@[simp]
theorem SetValuedSystem.betaHomeomorphRange_symm_apply
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    (system.betaHomeomorphRange hcontraction).symm
      ⟨system.boundaryMap hcontraction p, ⟨p, rfl⟩⟩ = p :=
  (system.betaHomeomorphRange hcontraction).symm_apply_apply p

theorem SetValuedSystem.boundaryMap_betaHomeomorphRange_symm
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (p : Set.range (system.boundaryMap hcontraction)) :
    system.boundaryMap hcontraction ((system.betaHomeomorphRange hcontraction).symm p) = p.val :=
  congrArg Subtype.val ((system.betaHomeomorphRange hcontraction).apply_symm_apply p)

/-- The full-image clause of Theorem 3.14, packaged as a homeomorphism of the state bundle. -/
noncomputable def SetValuedSystem.boundaryHomeomorphSelf
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain) :
    (system.domain × {n : E // ‖n‖ = 1}) ≃ₜ
      (system.domain × {n : E // ‖n‖ = 1}) :=
  (system.isEmbedding_boundaryMap hcontraction).toHomeomorphOfSurjective
    (system.boundaryMap_surjective_of_image_eq_domain hcontraction himage)

@[simp]
theorem SetValuedSystem.boundaryHomeomorphSelf_apply
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    system.boundaryHomeomorphSelf hcontraction himage p = system.boundaryMap hcontraction p :=
  rfl

theorem SetValuedSystem.continuous_boundaryHomeomorphSelf_symm
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain) :
    Continuous (system.boundaryHomeomorphSelf hcontraction himage).symm :=
  (system.boundaryHomeomorphSelf hcontraction himage).symm.continuous

end BoundedUncertainty
