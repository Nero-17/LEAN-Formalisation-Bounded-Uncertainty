import BoundedUncertainty.BoundaryAtlas
import BoundedUncertainty.HalfSpaceModel
import BoundedUncertainty.ChartedSpaceModelTransport
import BoundedUncertainty.DualBoundaryInterfaces
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! The actual dual ball is a compact topological manifold with boundary of
the ambient dimension. Its topology is the existing subspace topology.
The separately established C1 frontier is retained; no C1 atlas transition
claim is made in this topological manifold package. -/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

omit [CompleteSpace E] in
/-- The system's dimension assumption supplies positivity of the half-space model dimension. -/
def SetValuedSystem.finrankNeZero (system : SetValuedSystem (E := E) r s) :
    NeZero (Module.finrank ℝ E) :=
  ⟨ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)⟩

/-- Actual charts on the dual-ball subtype, with the standard d-dimensional half-space model. -/
noncomputable def SetValuedSystem.dualBallChartedSpace
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (x : E) :
    letI := system.finrankNeZero
    ChartedSpace (EuclideanHalfSpace (Module.finrank ℝ E)) (dualBall system.radius x) := by
  letI := system.finrankNeZero
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  letI : ChartedSpace {p : ℝ × (Fin (Module.finrank ℝ E - 1) → ℝ) // 0 ≤ p.1}
      (dualBall system.radius x) :=
    boundaryGraphChartedSpace (finiteDimensionalProductCoordinates E)
      (dualBall system.radius x) (fun y hy => Classical.choice
        (system.exists_dualBall_frontier_and_boundary_graphs hwhole hcontraction hpositive x
          ⟨y, hy⟩).2)
  exact chartedSpaceChangeModel (halfSpaceModelHomeomorph (Module.finrank ℝ E))

/-- The unnumbered dual-ball geometry assertion after Definition 4.13, on its
actual topology: compact, Hausdorff, second countable, a topological manifold
with boundary, star-shaped, and with the separately proved C1 frontier. -/
theorem SetValuedSystem.dualBall_manifold_with_boundary
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (x : E) :
    letI := system.finrankNeZero
    letI := system.dualBallChartedSpace hwhole hcontraction hpositive x
    CompactSpace (dualBall system.radius x) ∧
      T2Space (dualBall system.radius x) ∧
      SecondCountableTopology (dualBall system.radius x) ∧
      IsManifold (modelWithCornersEuclideanHalfSpace (Module.finrank ℝ E)) 0
        (dualBall system.radius x) ∧
      StarConvex ℝ x (dualBall system.radius x) ∧
      (∀ y : frontier (dualBall system.radius x),
        Nonempty (C1FrontierGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ)
          (dualBall system.radius x) y)) := by
  letI := system.finrankNeZero
  letI := system.dualBallChartedSpace hwhole hcontraction hpositive x
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  refine ⟨isCompact_iff_compactSpace.mp (system.isCompact_dualBall hwhole x),
    inferInstance, inferInstance, inferInstance, system.starConvex_dualBall hwhole hcontraction x, ?_⟩
  intro y
  exact (system.exists_dualBall_frontier_and_boundary_graphs hwhole hcontraction hpositive x y).1

end BoundedUncertainty
