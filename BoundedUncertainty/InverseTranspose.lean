import BoundedUncertainty.LinearLift
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Inverse transpose and its normalized lift

On a real Hilbert space, the inverse transpose is the adjoint of the inverse.
This file constructs it as a continuous linear equivalence and gives the exact
forward and inverse formulas on unit vectors. Taking `T` to be an already
constructed derivative equivalence then gives the linear part of the paper's
cotangent lift. No continuity in a varying base point is asserted here.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The inverse transpose of a continuous linear equivalence on a real Hilbert
space. Its inverse is the adjoint of the original equivalence. -/
noncomputable def inverseTranspose (T : E ≃L[ℝ] E) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.equivOfInverse'
    (ContinuousLinearMap.adjoint T.symm.toContinuousLinearMap)
    (ContinuousLinearMap.adjoint T.toContinuousLinearMap)
    (by
      rw [← ContinuousLinearMap.adjoint_comp, T.coe_comp_coe_symm,
        ContinuousLinearMap.adjoint_id])
    (by
      rw [← ContinuousLinearMap.adjoint_comp, T.coe_symm_comp_coe,
        ContinuousLinearMap.adjoint_id])

/-- The forward linear map is the adjoint of the inverse. -/
@[simp] theorem inverseTranspose_apply (T : E ≃L[ℝ] E) (n : E) :
    inverseTranspose T n = ContinuousLinearMap.adjoint T.symm.toContinuousLinearMap n :=
  rfl

/-- The inverse linear map is the adjoint of the original map. -/
@[simp] theorem inverseTranspose_symm_apply (T : E ≃L[ℝ] E) (n : E) :
    (inverseTranspose T).symm n = ContinuousLinearMap.adjoint T.toContinuousLinearMap n :=
  rfl

/-- The normalized cotangent direction in the paper: apply the inverse
transpose and divide by its norm. -/
theorem normalized_inverseTranspose_apply (T : E ≃L[ℝ] E)
    (n : {n : E // ‖n‖ = 1}) :
    ((normalizedLinearHomeomorph (inverseTranspose T) n : {n : E // ‖n‖ = 1}) : E) =
      ‖ContinuousLinearMap.adjoint T.symm.toContinuousLinearMap (n : E)‖⁻¹ •
        ContinuousLinearMap.adjoint T.symm.toContinuousLinearMap (n : E) :=
  rfl

/-- The inverse normalized cotangent direction: apply the transpose of the
original linear map and divide by its norm. -/
theorem normalized_inverseTranspose_symm_apply (T : E ≃L[ℝ] E)
    (n : {n : E // ‖n‖ = 1}) :
    (((normalizedLinearHomeomorph (inverseTranspose T)).symm n :
      {n : E // ‖n‖ = 1}) : E) =
      ‖ContinuousLinearMap.adjoint T.toContinuousLinearMap (n : E)‖⁻¹ •
        ContinuousLinearMap.adjoint T.toContinuousLinearMap (n : E) :=
  rfl

end BoundedUncertainty
