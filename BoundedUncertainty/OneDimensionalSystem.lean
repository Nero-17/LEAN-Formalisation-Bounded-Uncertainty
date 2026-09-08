import BoundedUncertainty.OneDimensionalCounterexample
import BoundedUncertainty.Section3Interfaces
import BoundedUncertainty.HigherLinearLift
import Mathlib.Topology.Instances.Real.Lemmas

/-! All Definition 3.1 hypotheses except dimension, and the actual composed boundary formula,
for the one-dimensional counterexample in Remark 3.18. -/
namespace BoundedUncertainty
open Set

theorem normalUpdate_radicand_real_unit (gradient n : ℝ) (hn : ‖n‖ = 1) :
    (inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1 = 1 := by
  rcases real_unit_cases n hn with rfl | rfl <;> simp [Real.norm_eq_abs, sq_abs]

theorem isRegularClosed_unitInterval : IsRegularClosed (Icc (-1 : ℝ) 1) := by
  rw [IsRegularClosed, interior_Icc, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

theorem linearLiftFormula_id_real (p : ℝ × ℝ) (hn : ‖p.2‖ = 1) :
    linearLiftFormula id (fun _ => (ContinuousLinearEquiv.refl ℝ ℝ : ℝ →L[ℝ] ℝ)) p = p := by
  simp only [linearLiftFormula, ContinuousLinearMap.ringInverse_equiv,
    ContinuousLinearMap.inverse_equiv]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, id_eq]
  simp only [hn, inv_one, one_smul]

noncomputable def intervalBoundaryFormula (p : ℝ × ℝ) : ℝ × ℝ :=
  exponentialMap intervalRadius (gradient intervalRadius)
    (linearLiftFormula id (fun _ => (ContinuousLinearEquiv.refl ℝ ℝ : ℝ →L[ℝ] ℝ)) p)

theorem intervalBoundaryFormula_eq_exponentialMap (p : ℝ × ℝ) (hn : ‖p.2‖ = 1) :
    intervalBoundaryFormula p = exponentialMap intervalRadius (fun x => -x) p := by
  rw [intervalBoundaryFormula, linearLiftFormula_id_real p hn]
  unfold exponentialMap
  rw [(hasGradientAt_intervalRadius p.1).gradient]

theorem bijOn_intervalBoundaryFormula : BijOn intervalBoundaryFormula
    ((Icc (-1 : ℝ) 1) ×ˢ {n : ℝ | ‖n‖ = 1})
    ((Icc (-1 : ℝ) 1) ×ˢ {n : ℝ | ‖n‖ = 1}) := by
  apply bijOn_exponentialMap_intervalRadius.congr
  intro p hp
  exact (intervalBoundaryFormula_eq_exponentialMap p hp.2).symm

/-- Every system assumption, with dimension one explicitly replacing dimension at least two. -/
theorem interval_example_all_hypotheses (order : ℕ) :
    Module.finrank ℝ ℝ = 1 ∧
    IsRegularClosed (Icc (-1 : ℝ) 1) ∧
    MapsTo (id : ℝ → ℝ) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
    Nonempty (AmbientDiffeomorphismOn order (Icc (-1 : ℝ) 1) (id : ℝ → ℝ)) ∧
    HasLocalExtensionOn order (Icc (-1 : ℝ) 1) intervalRadius ∧
    (0 : ℝ) < 1 / 2 ∧
    (∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ intervalRadius x ∧ intervalRadius x ≤ 1 / 2) ∧
    (∀ x ∈ Icc (-1 : ℝ) 1, Metric.closedBall (id x) (intervalRadius (id x)) ⊆ Icc (-1 : ℝ) 1) ∧
    BijOn intervalBoundaryFormula ((Icc (-1 : ℝ) 1) ×ˢ {n : ℝ | ‖n‖ = 1})
      ((Icc (-1 : ℝ) 1) ×ˢ {n : ℝ | ‖n‖ = 1}) ∧
    ¬ (∀ x ∈ Icc (-1 : ℝ) 1, ‖gradient intervalRadius x‖ < 1) := by
  exact ⟨Module.finrank_self ℝ, isRegularClosed_unitInterval, mapsTo_id _,
    ⟨ambientDiffeomorphismOn_id order _⟩,
    hasLocalExtensionOn_of_contDiff order _ _ (contDiff_intervalRadius order),
    by norm_num, intervalRadius_bounds, intervalRadius_ball_subset,
    bijOn_intervalBoundaryFormula, intervalRadius_not_strict_contraction⟩

end BoundedUncertainty
