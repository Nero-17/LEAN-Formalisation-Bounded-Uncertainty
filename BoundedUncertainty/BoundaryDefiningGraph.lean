import BoundedUncertainty.SequentialFrontierCriterion
import BoundedUncertainty.FrontierGraphReparametrization
import BoundedUncertainty.ZeroRadiusSecants

/-! Conversion of genuine pointwise C1 defining data into frontier graphs
with one fixed horizontal model for the whole normal bundle. -/

namespace BoundedUncertainty

open Set Topology Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual C1 defining data provide the graph witnesses used in Notation 3.3. -/
theorem nonempty_fixedModel_frontierGraph_of_c1BoundaryAt {B : Set E}
    (hregular : IsRegularClosed B) (boundary : (point : frontier B) → C1BoundaryAt B point)
    (point : frontier B) :
    Nonempty (C1FrontierGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ) B point) := by
  obtain ⟨chart⟩ := nonempty_c1FrontierGraphAt_of_sequential_normal_secants hregular
    (fun value => (boundary value).normal) (continuous_boundaryNormal boundary)
    (fun value => (boundary value).normal_unit) (by
      intro value first second hfirst hsecond
      exact (boundary value).tendsto_normalized_normal_chord hregular.isClosed
        (fun index => (first index : E)) (fun index => (second index : E))
        (continuous_subtype_val.tendsto value |>.comp hfirst)
        (continuous_subtype_val.tendsto value |>.comp hsecond)
        (fun index => (first index).property) (fun index => (second index).property)) point
  have hnonzero : InnerProductSpace.toDual ℝ E (boundary point).normal ≠ 0 := by
    intro hzero
    have h := congrArg (fun map : E →L[ℝ] ℝ => map (boundary point).normal) hzero
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq,
      (boundary point).normal_unit, one_pow, ContinuousLinearMap.zero_apply, one_ne_zero] at h
  exact ⟨chart.reparametrize
    (normalKernelEquiv (InnerProductSpace.toDual ℝ E (boundary point).normal) hnonzero)⟩

/-- A fixed-model frontier chart family selected from the proved existence theorem. -/
noncomputable def fixedModelFrontierGraph {B : Set E}
    (hregular : IsRegularClosed B) (boundary : (point : frontier B) → C1BoundaryAt B point)
    (point : frontier B) :
    C1FrontierGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ) B point :=
  Classical.choice (nonempty_fixedModel_frontierGraph_of_c1BoundaryAt hregular boundary point)

end BoundedUncertainty
