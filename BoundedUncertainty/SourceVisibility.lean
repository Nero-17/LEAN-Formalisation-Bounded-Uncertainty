import BoundedUncertainty.BoundaryContributors
import BoundedUncertainty.Section3Interfaces
import BoundedUncertainty.DiffeomorphismSetGeometry

/-! Source visibility (Assumption 4.1) and existence of actual boundary contributors. -/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {r s : ℕ}

/-- Every source boundary point has a constituent ball meeting the image boundary. -/
def SetValuedSystem.SourceVisible (system : SetValuedSystem (E := E) r s)
    (A : Set E) : Prop :=
  ∀ x ∈ frontier A, ∃ z,
    z ∈ Metric.closedBall (system.map x) (system.radius (system.map x)) ∧
    z ∈ frontier (setValuedImage system.map system.radius A)

omit [CompleteSpace E] in
/-- At an image boundary point, membership in a constituent ball is necessarily contact. -/
theorem SetValuedSystem.isContributingPair_of_mem_constituent
    (system : SetValuedSystem (E := E) r s) (A : Set E) (x z : E)
    (hx : x ∈ A)
    (hball : z ∈ Metric.closedBall (system.map x) (system.radius (system.map x)))
    (hz : z ∈ frontier (setValuedImage system.map system.radius A)) :
    IsContributingPair system.radius (system.map '' A) (system.map x) z := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  rw [setValuedImage_eq_inflation] at hz
  apply (isContributingPair_iff_dist _ _ _ _).mpr
  exact ⟨⟨x, hx, rfl⟩, hz, le_antisymm hball
    (radius_le_dist_of_frontier_inflation _ _ _ _ hz ⟨x, hx, rfl⟩)⟩

omit [CompleteSpace E] in
/-- Visibility is exactly existence of contributing pairs for every source boundary point. -/
theorem SetValuedSystem.sourceVisible_iff_contributingPair
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hclosed : IsClosed A) :
    system.SourceVisible A ↔ ∀ x ∈ frontier A, ∃ z,
      IsContributingPair system.radius (system.map '' A) (system.map x) z := by
  constructor
  · intro hvisible x hx
    obtain ⟨z, hball, hz⟩ := hvisible x hx
    exact ⟨z, system.isContributingPair_of_mem_constituent A x z
      (hclosed.frontier_subset hx) hball hz⟩
  · intro hcontact x hx
    obtain ⟨z, hz⟩ := hcontact x hx
    refine ⟨z, Metric.isClosed_closedBall.frontier_subset hz.2.2, ?_⟩
    simpa only [setValuedImage_eq_inflation] using hz.2.1

/-- Compactness gives a contributor on the actual source boundary for every recipient.
No source visibility or boundary smoothness is required for this direction. -/
theorem SetValuedSystem.exists_source_frontier_contributingPair
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (z : E) (hz : z ∈ frontier (setValuedImage system.map system.radius A)) :
    ∃ x ∈ frontier A,
      IsContributingPair system.radius (system.map '' A) (system.map x) z := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  have himage : system.map '' A ⊆ system.domain := by
    rintro y ⟨x, hx, rfl⟩
    exact system.map_into_domain (hA hx)
  rw [setValuedImage_eq_inflation] at hz
  obtain ⟨y, hy, hcontact⟩ := exists_mem_sphere_of_mem_frontier_inflation
    system.radius (system.map '' A) (system.diffeomorphism.isCompact_image hA hcompact)
    (system.radius_extension.continuousOn.mono himage)
    (fun y hy => system.radius_nonneg y (himage hy)) z hz
  have hyfrontier := system.contributor_mem_frontier hcontraction
    (system.map '' A) himage y z hy hz hcontact
  rw [system.diffeomorphism.frontier_image system.map_order_pos hA hcompact] at hyfrontier
  obtain ⟨x, hx, rfl⟩ := hyfrontier
  exact ⟨x, hx, (isContributingPair_iff_dist _ _ _ _).mpr ⟨hy, hz, hcontact⟩⟩

end BoundedUncertainty
