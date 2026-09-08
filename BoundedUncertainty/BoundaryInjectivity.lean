import BoundedUncertainty.BoundaryContinuity
import BoundedUncertainty.ExponentialInjectivity

/-!
# Injectivity of the actual boundary map

Theorem 3.14's injectivity conclusion follows from the linear lift's
injectivity and the exponential lift's injectivity on centres in `f(X)`.
No closed-image or full-space-image assumption is used.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

theorem SetValuedSystem.boundaryMap_injective
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    Function.Injective (system.boundaryMap hcontraction) := by
  intro p q heq
  apply system.linearLift_injective
  apply system.exponentialLift_injOn_image hcontraction
  · exact system.linearLift_position_mem_image p
  · exact system.linearLift_position_mem_image q
  · apply Prod.ext
    · exact congrArg (fun output : system.domain × {n : E // ‖n‖ = 1} =>
        (output.1 : E)) heq
    · exact congrArg (fun output : system.domain × {n : E // ‖n‖ = 1} =>
        output.2) heq

end BoundedUncertainty
