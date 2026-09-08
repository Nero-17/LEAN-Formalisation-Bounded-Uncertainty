import BoundedUncertainty.InverseTranspose
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuous families of normalized linear lifts

Inversion is continuous for a family of invertible operators whose forward
operators vary continuously in operator norm. Consequently the inverse transpose
and its normalized action on unit vectors vary jointly continuously. Continuity
of the inverse operators is a conclusion, not an additional hypothesis.
-/

namespace BoundedUncertainty

variable {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E]

/-- A continuously varying family of invertible operators has a continuously
varying inverse. The assumption is only on the forward operators. -/
theorem continuous_linearEquiv_symm [CompleteSpace E] (T : P → E ≃L[ℝ] E)
    (hT : Continuous (fun p => (T p : E →L[ℝ] E))) :
    Continuous (fun p => ((T p).symm : E →L[ℝ] E)) := by
  have hinverse : Continuous (fun p => Ring.inverse (T p : E →L[ℝ] E)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun p => (T p : E →L[ℝ] E)) (x := p)
      (NormedRing.inverse_continuousAt (T p).toUnit) hT.continuousAt
  simpa only [ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]
    using hinverse

/-- Normalization of a continuous family of invertible operators is jointly
continuous in the parameter and unit vector. -/
theorem continuous_normalizedLinearMap_family (T : P → E ≃L[ℝ] E)
    (hT : Continuous (fun p => (T p : E →L[ℝ] E))) :
    Continuous (fun pn : P × {n : E // ‖n‖ = 1} =>
      normalizedLinearMap (T pn.1) pn.2.1) := by
  have happly : Continuous (fun pn : P × {n : E // ‖n‖ = 1} => T pn.1 pn.2.1) :=
    (hT.comp continuous_fst).clm_apply (continuous_subtype_val.comp continuous_snd)
  exact (happly.norm.inv₀ (fun pn =>
    norm_ne_zero_iff.mpr (linearMap_unit_ne_zero (T pn.1) pn.2.2))).smul happly

/-- Subtype-valued form of joint continuity for the normalized linear action. -/
theorem continuous_normalizedLinearHomeomorph_family (T : P → E ≃L[ℝ] E)
    (hT : Continuous (fun p => (T p : E →L[ℝ] E))) :
    Continuous (fun pn : P × {n : E // ‖n‖ = 1} =>
      normalizedLinearHomeomorph (T pn.1) pn.2) :=
  (continuous_normalizedLinearMap_family T hT).subtype_mk _

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The inverse transpose depends continuously on a continuously varying
invertible operator, in the operator norm topology. -/
theorem continuous_inverseTranspose (T : P → E ≃L[ℝ] E)
    (hT : Continuous (fun p => (T p : E →L[ℝ] E))) :
    Continuous (fun p => (inverseTranspose (T p) : E →L[ℝ] E)) := by
  change Continuous (fun p =>
    ContinuousLinearMap.adjoint ((T p).symm : E →L[ℝ] E))
  exact ContinuousLinearMap.adjoint.continuous.comp (continuous_linearEquiv_symm T hT)

/-- The paper's normalized inverse-transpose direction is jointly continuous
in the base parameter and the incoming unit normal. -/
theorem continuous_normalizedInverseTranspose_family (T : P → E ≃L[ℝ] E)
    (hT : Continuous (fun p => (T p : E →L[ℝ] E))) :
    Continuous (fun pn : P × {n : E // ‖n‖ = 1} =>
      normalizedLinearMap (inverseTranspose (T pn.1)) pn.2.1) :=
  continuous_normalizedLinearMap_family (fun p => inverseTranspose (T p))
    (continuous_inverseTranspose T hT)

/-- Unit-vector-valued joint continuity for the normalized inverse transpose. -/
theorem continuous_normalizedInverseTransposeHomeomorph_family (T : P → E ≃L[ℝ] E)
    (hT : Continuous (fun p => (T p : E →L[ℝ] E))) :
    Continuous (fun pn : P × {n : E // ‖n‖ = 1} =>
      normalizedLinearHomeomorph (inverseTranspose (T pn.1)) pn.2) :=
  continuous_normalizedLinearHomeomorph_family (fun p => inverseTranspose (T p))
    (continuous_inverseTranspose T hT)

end InnerProductSpace

end BoundedUncertainty
