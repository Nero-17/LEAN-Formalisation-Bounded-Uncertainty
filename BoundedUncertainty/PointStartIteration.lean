import BoundedUncertainty.IteratedBoundaryInclusion
import BoundedUncertainty.BoundaryFibre

/-! The point-start initialization after Proposition 4.11, followed by all
finite iterates. Later frontiers are contained in the projected transported
fibre; equality is not asserted without additional visibility hypotheses. -/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem setValuedIterate_image (f : E → E) (radius : E → ℝ) (A : Set E) (n : ℕ) :
    setValuedIterate f radius n (setValuedImage f radius A) =
      setValuedIterate f radius (n + 1) A := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (setValuedImage f radius) ih

variable {r s : ℕ}

/-- A positive first radius suffices: no smoothness of later frontiers is needed. -/
theorem SetValuedSystem.frontier_pointStartIterate_subset_projected_fibre
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (x : system.domain) (hpositive : 0 < system.radius (system.map x)) (n : ℕ) :
    frontier (setValuedIterate system.map system.radius (n + 1) {(x : E)}) ⊆
      Prod.fst '' (system.boundaryFormulaOnAmbient^[n + 1] ''
        ({(x : E)} ×ˢ {v : E | ‖v‖ = 1})) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  intro z hz
  rw [← setValuedIterate_image, setValuedImage_singleton] at hz
  obtain ⟨p, ⟨q, ⟨a, rfl⟩, rfl⟩, hposition⟩ :=
    system.frontier_setValuedIterate_subset_projected_boundaryNormalInput hcontraction
      (Metric.closedBall (system.map x) (system.radius (system.map x)))
      (system.ball_into_domain x x.property) (isCompact_closedBall _ _)
      (fun a => C1BoundaryAt.closedBall (system.map x) (system.radius (system.map x)) (a : E) hpositive
        (Metric.frontier_closedBall_subset_sphere a.property)) n hz
  have hnormal : ((a : E), (C1BoundaryAt.closedBall (system.map x)
      (system.radius (system.map x)) (a : E) hpositive
      (Metric.frontier_closedBall_subset_sphere a.property)).normal) ∈
      closedBallOutwardNormalBundle (system.map x) (system.radius (system.map x))
        hpositive := ⟨a, rfl⟩
  rw [← system.image_boundaryFormula_fibre_eq_closedBallOutwardNormalBundle x hpositive
    (hcontraction.norm_radiusGradientOnAmbient _ (system.map_into_domain x.property))]
    at hnormal
  obtain ⟨⟨source, v⟩, ⟨hsource, _⟩, hequal⟩ := hnormal
  have hsourceEq : source = x := hsource
  subst source
  refine ⟨system.boundaryFormulaOnAmbient^[n + 1] ((x : E), (v : E)),
    ⟨((x : E), (v : E)), ⟨rfl, v.property⟩, rfl⟩, ?_⟩
  rw [Function.iterate_succ_apply]
  rw [system.boundaryFormulaOnAmbient_apply (x, v)]
  rw [hequal]
  have hiterate := system.iterate_boundaryFormulaOnAmbient_eq_boundaryMap hcontraction n
    (system.boundaryNormalInput _ (system.ball_into_domain x x.property)
      (fun a => C1BoundaryAt.closedBall (system.map x) (system.radius (system.map x))
        (a : E) hpositive (Metric.frontier_closedBall_subset_sphere a.property)) a)
  simp only [SetValuedSystem.boundaryNormalInput] at hiterate
  exact (congrArg Prod.fst hiterate).trans hposition

end BoundedUncertainty
