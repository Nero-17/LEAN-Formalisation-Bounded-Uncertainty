import BoundedUncertainty.DualInverseBoundary
import BoundedUncertainty.BoundaryDefiningGraph

/-!
Final graph-notation bridges for the dual construction. The preimage chart
family in Theorem 4.17 is constructed from actual C1 defining data, using one
fixed horizontal model. It is not an additional smoothness hypothesis.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

omit [CompleteSpace E] in
/-- Boundary attainment makes the actual union closed, without compactness of the source. -/
theorem SetValuedSystem.isClosed_dualInflation_of_boundary_nearest
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (A : Set E) (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A) :
    IsClosed (dualInflation system.radius A) := by
  apply frontier_subset_iff_isClosed.mp
  intro y hy
  obtain ⟨x, hx, hdist⟩ := hnearest y hy
  have hlevel := system.infDist_eq_radius_of_mem_frontier_dualInflation hwhole A ⟨x, hx⟩ y hy
  exact (mem_dualInflation system.radius A y).mpr
    ⟨x, hx, ((dist_comm x y).trans (hdist.trans hlevel)).le⟩

/-- Closedness of the union and regular closedness of its constituents suffice. -/
theorem SetValuedSystem.isRegularClosed_dualInflation_of_boundary_nearest
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A) :
    IsRegularClosed (dualInflation system.radius A) := by
  apply Subset.antisymm (closure_minimal interior_subset
    (system.isClosed_dualInflation_of_boundary_nearest hwhole A hnearest))
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_dualInflation system.radius A y).mp hy
  have hsubset : dualBall system.radius x ⊆ dualInflation system.radius A := by
    intro w hw
    exact (mem_dualInflation system.radius A w).mpr ⟨x, hx, hw⟩
  apply closure_mono (interior_mono hsubset)
  rw [system.isRegularClosed_dualBall hwhole hcontraction x (fun w _ => hpositive w)]
  exact hxy

theorem SetValuedSystem.isRegularClosed_dualSetMap_of_boundary_nearest
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A) :
    IsRegularClosed (dualSetMap system.map system.radius A) := by
  rw [dualSetMap_eq_preimage]
  exact system.isRegularClosed_preimage_of_wholeSpace hwhole hself _
    (system.isRegularClosed_dualInflation_of_boundary_nearest hwhole hcontraction hpositive A hnearest)

theorem SetValuedSystem.isRegularClosed_dualSetMap_of_compact
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hcompact : IsCompact A) :
    IsRegularClosed (dualSetMap system.map system.radius A) := by
  rw [dualSetMap_eq_preimage]
  exact system.isRegularClosed_preimage_of_wholeSpace hwhole hself _
    (system.isRegularClosed_dualInflation hwhole hcontraction hpositive A hcompact)

/-- The dual-ball frontier has genuine C1 hypersurface and one-sided domain charts. -/
theorem SetValuedSystem.exists_dualBall_frontier_and_boundary_graphs
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (x : E) (y : frontier (dualBall system.radius x)) :
    Nonempty (C1FrontierGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ)
      (dualBall system.radius x) y) ∧
    Nonempty (C1BoundaryGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ)
      (dualBall system.radius x) y) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  have hregular := system.isRegularClosed_dualBall hwhole hcontraction x (fun w _ => hpositive w)
  let boundary : (w : frontier (dualBall system.radius x)) → C1BoundaryAt (dualBall system.radius x) w :=
    fun w => Classical.choice (system.exists_C1BoundaryAt_dualBall hwhole hcontraction x w
      w.property (hpositive w))
  obtain ⟨chart⟩ := nonempty_fixedModel_frontierGraph_of_c1BoundaryAt hregular boundary y
  exact ⟨⟨chart⟩, chart.nonempty_boundaryGraph hregular⟩

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Compact specialization of Theorem 4.17 with the preimage charts constructed. -/
theorem SetValuedSystem.exists_dualSet_frontierCharts_and_inverse_boundary_correspondence
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hcompact : IsCompact A) (hregular : IsRegularClosed A)
    (original : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (inflated : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    ∃ source : (x : frontier (dualSetMap system.map system.radius A)) →
        C1FrontierGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ)
          (dualSetMap system.map system.radius A) x,
      system.boundaryInverseOnAmbient hcontraction '' inwardNormalBundle A hregular original =
        inwardNormalBundle (dualSetMap system.map system.radius A)
          (system.isRegularClosed_dualSetMap_of_compact hwhole hself hcontraction hpositive A hcompact)
          source := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  have hdualregular := system.isRegularClosed_dualInflation hwhole hcontraction hpositive A hcompact
  have hdualsetregular := system.isRegularClosed_dualSetMap_of_compact hwhole hself hcontraction
    hpositive A hcompact
  let preimageBoundary : (x : frontier (dualSetMap system.map system.radius A)) →
      C1BoundaryAt (dualSetMap system.map system.radius A) x := fun x => Classical.choice
    (system.exists_C1BoundaryAt_dualSetMap hwhole hself A
      (fun y => (inflated y).toC1BoundaryAt hdualregular) x x.property)
  refine ⟨fixedModelFrontierGraph hdualsetregular preimageBoundary, ?_⟩
  apply system.image_boundaryInverseOnAmbient_inwardNormalBundle_dualSetMap hwhole hself
    hcontraction hpositive A hregular hdualregular hdualsetregular original inflated
    (fixedModelFrontierGraph hdualsetregular preimageBoundary) ?_ hvisible
  intro y hy
  rcases A.eq_empty_or_nonempty with hempty | hnonempty
  · simp only [hempty, dualInflation_empty, frontier_empty, mem_empty_iff_false] at hy
  · obtain ⟨x, hx, hdist⟩ := hcompact.exists_infDist_eq_dist hnonempty y
    exact ⟨x, hx, hdist.symm⟩

/-- Theorem 4.16 under the two-sided nearest-point conditions, without compactness. -/
theorem SetValuedSystem.image_exponentialMap_inwardNormalBundle_of_two_sided_nearest
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hregular : IsRegularClosed A)
    (original : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (inflated : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    exponentialMap system.radius system.radiusGradientOnAmbient ''
      inwardNormalBundle (dualInflation system.radius A)
        (system.isRegularClosed_dualInflation_of_boundary_nearest hwhole hcontraction hpositive A hnearest)
        inflated = inwardNormalBundle A hregular original :=
  system.image_exponentialMap_inwardNormalBundle_dualInflation hwhole hcontraction hpositive A
    hregular _ original inflated hnearest hvisible

/-- Theorem 4.17 with derived target regularity and constructed preimage charts, without compactness. -/
theorem SetValuedSystem.exists_dualSet_frontierCharts_and_inverse_correspondence_of_two_sided_nearest
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hregular : IsRegularClosed A)
    (original : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (inflated : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    ∃ source : (x : frontier (dualSetMap system.map system.radius A)) →
        C1FrontierGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ)
          (dualSetMap system.map system.radius A) x,
      system.boundaryInverseOnAmbient hcontraction '' inwardNormalBundle A hregular original =
        inwardNormalBundle (dualSetMap system.map system.radius A)
          (system.isRegularClosed_dualSetMap_of_boundary_nearest hwhole hself hcontraction hpositive A hnearest)
          source := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  have hdualregular := system.isRegularClosed_dualInflation_of_boundary_nearest hwhole hcontraction
    hpositive A hnearest
  have hdualsetregular := system.isRegularClosed_dualSetMap_of_boundary_nearest hwhole hself
    hcontraction hpositive A hnearest
  let preimageBoundary : (x : frontier (dualSetMap system.map system.radius A)) →
      C1BoundaryAt (dualSetMap system.map system.radius A) x := fun x => Classical.choice
    (system.exists_C1BoundaryAt_dualSetMap hwhole hself A
      (fun y => (inflated y).toC1BoundaryAt hdualregular) x x.property)
  refine ⟨fixedModelFrontierGraph hdualsetregular preimageBoundary, ?_⟩
  exact system.image_boundaryInverseOnAmbient_inwardNormalBundle_dualSetMap hwhole hself
    hcontraction hpositive A hregular hdualregular hdualsetregular original inflated
    (fixedModelFrontierGraph hdualsetregular preimageBoundary) hnearest hvisible

end BoundedUncertainty
