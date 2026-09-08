import BoundedUncertainty.BoundaryNormalContinuity

/-! The forward implication and topological reduction of Theorem 4.9.
The converse C1 conclusion is not asserted in this module. -/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {r s : ℕ}

/-- A genuine contact determines Gamma without any smoothness at the recipient. -/
theorem SetValuedSystem.boundaryProjection_eq_of_contributingPair
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x) (x : frontier A) (z : E)
    (hcontact : IsContributingPair system.radius (system.map '' A) (system.map x) z) :
    system.boundaryProjection A hA source x = z := by
  obtain ⟨imageBoundary, hnormal⟩ := system.exists_imageBoundary A hA hcompact x (source x)
  have himage : system.map '' A ⊆ system.domain := by
    rintro y ⟨a, ha, rfl⟩
    exact system.map_into_domain (hA ha)
  have hposition := system.recipient_position_eq_normalUpdate hcontraction
    (system.map '' A) himage (system.map x) z imageBoundary hcontact.2.1
    (Metric.frontier_closedBall_subset_sphere hcontact.2.2)
  rw [hnormal] at hposition
  exact hposition.symm

/-- Visibility and source smoothness alone identify the range of Gamma. -/
theorem SetValuedSystem.range_boundaryProjection_of_sourceVisible
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x) (hvisible : system.SourceVisible A) :
    range (system.boundaryProjection A hA source) =
      frontier (setValuedImage system.map system.radius A) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨w, hcontact⟩ :=
      (system.sourceVisible_iff_contributingPair A hcompact.isClosed).mp hvisible x x.property
    rw [system.boundaryProjection_eq_of_contributingPair hcontraction A hA hcompact source x w hcontact,
      setValuedImage_eq_inflation]
    exact hcontact.2.1
  · intro hz
    obtain ⟨x, hx, hcontact⟩ := system.exists_source_frontier_contributingPair
      hcontraction A hA hcompact z hz
    exact ⟨⟨x, hx⟩, system.boundaryProjection_eq_of_contributingPair
      hcontraction A hA hcompact source ⟨x, hx⟩ z hcontact⟩

/-- Injectivity of Gamma gives unique contributors before recipient C1 is established. -/
theorem SetValuedSystem.contributor_eq_of_boundaryProjection_injective
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (hinjective : Function.Injective (system.boundaryProjection A hA source))
    (y₁ y₂ z : E)
    (hfirst : IsContributingPair system.radius (system.map '' A) y₁ z)
    (hsecond : IsContributingPair system.radius (system.map '' A) y₂ z) : y₁ = y₂ := by
  have himage : system.map '' A ⊆ system.domain := by
    rintro y ⟨a, ha, rfl⟩
    exact system.map_into_domain (hA ha)
  have hfrontier (y : E) (hcontact : IsContributingPair system.radius (system.map '' A) y z) :
      y ∈ system.map '' frontier A := by
    rw [← system.diffeomorphism.frontier_image system.map_order_pos hA hcompact]
    exact system.contributor_mem_frontier hcontraction (system.map '' A) himage y z
      hcontact.1 hcontact.2.1 (Metric.frontier_closedBall_subset_sphere hcontact.2.2)
  obtain ⟨x₁, hx₁, rfl⟩ := hfrontier y₁ hfirst
  obtain ⟨x₂, hx₂, rfl⟩ := hfrontier y₂ hsecond
  have heq := hinjective
    ((system.boundaryProjection_eq_of_contributingPair hcontraction A hA hcompact
      source ⟨x₁, hx₁⟩ z hfirst).trans
      (system.boundaryProjection_eq_of_contributingPair hcontraction A hA hcompact
        source ⟨x₂, hx₂⟩ z hsecond).symm)
  exact congrArg system.map (congrArg Subtype.val heq)

/-- The forward implication concerns the raw Gamma, which does not require recipient data to define. -/
theorem SetValuedSystem.boundaryProjection_bijective_onto_frontier
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (recipient : (z : frontier (setValuedImage system.map system.radius A)) →
      C1BoundaryAt (setValuedImage system.map system.radius A) z)
    (hvisible : system.SourceVisible A) :
    Function.Injective (system.boundaryProjection A hA source) ∧
      range (system.boundaryProjection A hA source) =
        frontier (setValuedImage system.map system.radius A) := by
  have hbijective := system.projectedBoundaryMap_bijective hcontraction A hA hcompact
    source recipient hvisible
  constructor
  · intro x y hxy
    exact hbijective.1 (Subtype.ext hxy)
  · ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact system.boundaryFormula_normalInput_position_mem_frontier hcontraction A hA hcompact
        source recipient hvisible x
    · intro hz
      obtain ⟨x, hx⟩ := hbijective.2 ⟨z, hz⟩
      exact ⟨x, congrArg Subtype.val hx⟩

/-- The topological reduction in the converse uses no recipient C1 assumption. -/
noncomputable def SetValuedSystem.boundaryProjectionHomeomorph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (hinjective : Function.Injective (system.boundaryProjection A hA source))
    (hrange : range (system.boundaryProjection A hA source) =
      frontier (setValuedImage system.map system.radius A)) :
    frontier A ≃ₜ frontier (setValuedImage system.map system.radius A) := by
  letI : CompactSpace (frontier A) :=
    isCompact_iff_compactSpace.mp
      (hcompact.of_isClosed_subset isClosed_frontier hcompact.isClosed.frontier_subset)
  let projection : frontier A → frontier (setValuedImage system.map system.radius A) :=
    fun x => ⟨system.boundaryProjection A hA source x, hrange.subset ⟨x, rfl⟩⟩
  have hbijective : Function.Bijective projection := by
    constructor
    · intro x y hxy
      exact hinjective (congrArg Subtype.val hxy)
    · intro z
      obtain ⟨x, hx⟩ := hrange.symm.subset z.property
      exact ⟨x, Subtype.ext hx⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective projection hbijective)
    ((system.continuous_boundaryProjection hcontraction A hA source).subtype_mk _)

theorem SetValuedSystem.boundaryProjectionHomeomorph_apply
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (hinjective : Function.Injective (system.boundaryProjection A hA source))
    (hrange : range (system.boundaryProjection A hA source) =
      frontier (setValuedImage system.map system.radius A)) (x : frontier A) :
    ((system.boundaryProjectionHomeomorph hcontraction A hA hcompact source hinjective hrange x) : E) =
      system.boundaryProjection A hA source x := rfl

end BoundedUncertainty
