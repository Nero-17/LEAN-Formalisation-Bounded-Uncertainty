import BoundedUncertainty.DualBallGeometry
import BoundedUncertainty.DualInflationScope

/-!
Compactness and regular closedness of the union-defined dual inflation.
The empty input is handled separately when using the real infimum distance.
Positive radius is needed only for the constituent boundary regularity.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.isClosed_dualInflation_of_compact
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (A : Set E) (hcompact : IsCompact A) : IsClosed (dualInflation system.radius A) := by
  rcases A.eq_empty_or_nonempty with hempty | hnonempty
  · rw [hempty, dualInflation_empty]
    exact isClosed_empty
  · rw [dualInflation_eq_infDist_sublevel_of_isCompact system.radius A hcompact hnonempty]
    have hcontinuous : Continuous system.radius := continuousOn_univ.mp
      (hwhole ▸ system.radius_extension.continuousOn)
    exact isClosed_le (Metric.continuous_infDist_pt A) hcontinuous

omit [CompleteSpace E] in
theorem SetValuedSystem.isCompact_dualInflation
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (A : Set E) (hcompact : IsCompact A) : IsCompact (dualInflation system.radius A) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : E)
  apply (isCompact_closedBall (0 : E) (system.radius_bound + R)).of_isClosed_subset
    (system.isClosed_dualInflation_of_compact hwhole A hcompact)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_dualInflation system.radius A y).mp hy
  have hbound := system.radius_le_bound y (hwhole ▸ mem_univ y)
  have hsource : dist x (0 : E) ≤ R := hR hx
  calc
    dist y (0 : E) ≤ dist y x + dist x (0 : E) := dist_triangle y x 0
    _ = dist x y + dist x (0 : E) := by rw [dist_comm y x]
    _ ≤ system.radius_bound + R := add_le_add (hxy.trans hbound) hsource

theorem SetValuedSystem.isRegularClosed_dualInflation
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hcompact : IsCompact A) : IsRegularClosed (dualInflation system.radius A) := by
  apply Subset.antisymm
    (closure_minimal interior_subset (system.isClosed_dualInflation_of_compact hwhole A hcompact))
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_dualInflation system.radius A y).mp hy
  have hsubset : dualBall system.radius x ⊆ dualInflation system.radius A := by
    intro w hw
    exact (mem_dualInflation system.radius A w).mpr ⟨x, hx, hw⟩
  apply closure_mono (interior_mono hsubset)
  rw [system.isRegularClosed_dualBall hwhole hcontraction x (fun w _ => hpositive w)]
  exact hxy

end BoundedUncertainty
