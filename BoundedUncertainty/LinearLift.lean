import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Normalized linear lift

This file formalizes the linear algebra used in the normalized tangent/cotangent
lift of Section 3. The input is an arbitrary continuous linear equivalence.
Identifying this equivalence with the inverse transpose derivative of the
manuscript's map is a separate obligation, not an assumption hidden here.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply an invertible linear map and normalize the resulting vector. -/
noncomputable def normalizedLinearMap (T : E ≃L[ℝ] E) (n : E) : E :=
  ‖T n‖⁻¹ • T n

/-- An invertible linear map cannot vanish on a unit vector. -/
theorem linearMap_unit_ne_zero (T : E ≃L[ℝ] E) {n : E} (hn : ‖n‖ = 1) :
    T n ≠ 0 := by
  intro h
  have : n = 0 := T.injective (by simpa using h)
  simp [this] at hn

/-- Normalization gives a unit vector when the input is a unit vector. -/
theorem norm_normalizedLinearMap (T : E ≃L[ℝ] E) {n : E} (hn : ‖n‖ = 1) :
    ‖normalizedLinearMap T n‖ = 1 := by
  exact norm_smul_inv_norm (linearMap_unit_ne_zero T hn)

/-- The normalized inverse linear map reverses the normalized forward map. -/
theorem normalizedLinearMap_symm_apply (T : E ≃L[ℝ] E) {n : E} (hn : ‖n‖ = 1) :
    normalizedLinearMap T.symm (normalizedLinearMap T n) = n := by
  simp only [normalizedLinearMap, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), hn,
    mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (linearMap_unit_ne_zero T hn)), one_smul]

/-- The normalized forward map reverses the normalized inverse linear map. -/
theorem normalizedLinearMap_apply_symm (T : E ≃L[ℝ] E) {n : E} (hn : ‖n‖ = 1) :
    normalizedLinearMap T (normalizedLinearMap T.symm n) = n := by
  simpa using normalizedLinearMap_symm_apply T.symm hn

/-- Continuity of the normalized linear map restricted to the unit vectors. -/
theorem continuous_normalizedLinearMap_unit (T : E ≃L[ℝ] E) :
    Continuous (fun n : {n : E // ‖n‖ = 1} => normalizedLinearMap T n.1) := by
  unfold normalizedLinearMap
  apply Continuous.smul
  · apply Continuous.inv₀
    · exact (T.continuous.comp continuous_subtype_val).norm
    · intro n
      exact norm_ne_zero_iff.mpr (linearMap_unit_ne_zero T n.2)
  · exact T.continuous.comp continuous_subtype_val

/-- An invertible linear map induces a homeomorphism on the unit vectors.
The inverse is the normalization of the inverse linear map. -/
noncomputable def normalizedLinearHomeomorph (T : E ≃L[ℝ] E) :
    {n : E // ‖n‖ = 1} ≃ₜ {n : E // ‖n‖ = 1} where
  toFun n := ⟨normalizedLinearMap T n.1, norm_normalizedLinearMap T n.2⟩
  invFun n := ⟨normalizedLinearMap T.symm n.1, norm_normalizedLinearMap T.symm n.2⟩
  left_inv n := Subtype.ext (normalizedLinearMap_symm_apply T n.2)
  right_inv n := Subtype.ext (normalizedLinearMap_apply_symm T n.2)
  continuous_toFun := (continuous_normalizedLinearMap_unit T).subtype_mk _
  continuous_invFun := (continuous_normalizedLinearMap_unit T.symm).subtype_mk _

/-- In particular, the normalized lift is bijective on the unit vectors. -/
theorem normalizedLinearMap_bijective (T : E ≃L[ℝ] E) :
    Function.Bijective (normalizedLinearHomeomorph T) :=
  (normalizedLinearHomeomorph T).bijective

end BoundedUncertainty
