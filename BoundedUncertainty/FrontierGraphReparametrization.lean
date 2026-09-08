import BoundedUncertainty.C1FrontierGraph
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Horizontal reparametrisation makes the local graph model independent
of the marked point, as required by the normal-bundle notation. -/

namespace BoundedUncertainty

open Set

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Replace the horizontal graph space by a continuously linearly equivalent one. -/
noncomputable def C1FrontierGraphAt.reparametrize {B : Set E} {point : E}
    (chart : C1FrontierGraphAt (F := F) B point) (equivalence : F ≃L[ℝ] G) :
    C1FrontierGraphAt (F := G) B point where
  coordinates := chart.coordinates.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr equivalence)
  neighborhood := chart.neighborhood
  isOpen_neighborhood := chart.isOpen_neighborhood
  mem_neighborhood := chart.mem_neighborhood
  graphDomain := equivalence.symm ⁻¹' chart.graphDomain
  isOpen_graphDomain := chart.isOpen_graphDomain.preimage equivalence.symm.continuous
  zero_mem_graphDomain := by simpa using chart.zero_mem_graphDomain
  graph := fun value => chart.graph (equivalence.symm value)
  contDiffOn_graph := chart.contDiffOn_graph.comp equivalence.symm.contDiff.contDiffOn
    (fun _ hvalue => hvalue)
  graph_zero := by simpa using chart.graph_zero
  mem_frontier_iff := by
    intro value hvalue
    simpa only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply, ContinuousLinearEquiv.symm_apply_apply] using
      chart.mem_frontier_iff value hvalue

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] in
/-- Every nonzero real covector kernel has the fixed codimension-one model. -/
noncomputable def normalKernelEquiv [FiniteDimensional ℝ E] (normal : E →L[ℝ] ℝ)
    (hnonzero : normal ≠ 0) : normal.ker ≃L[ℝ] (Fin (Module.finrank ℝ E - 1) → ℝ) :=
  (LinearEquiv.ofFinrankEq normal.ker (Fin (Module.finrank ℝ E - 1) → ℝ) (by
    have hlinear : normal.toLinearMap ≠ 0 := by
      intro hzero
      apply hnonzero
      ext point
      exact congrArg (fun map : E →ₗ[ℝ] ℝ => map point) hzero
    have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hlinear
    rw [Module.finrank_pi, Fintype.card_fin]
    omega)).toContinuousLinearEquiv

end BoundedUncertainty
