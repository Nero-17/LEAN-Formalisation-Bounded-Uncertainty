import BoundedUncertainty.RecipientSecants
import BoundedUncertainty.SequentialFrontierCriterion
import BoundedUncertainty.ForwardNormalBundle
import BoundedUncertainty.BoundaryDefiningGraph

/-!
Theorem 4.9 for the actual set-valued system. Injectivity of Gamma gives C1
recipient boundary data through the proved recipient secants and the actual
regular-closed frontier criterion. Under source visibility this is equivalent
to recipient C1 regularity. No recipient chart or secant condition is assumed.
-/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- Injectivity onto the actual recipient frontier gives its C1 boundary at every point. -/
theorem SetValuedSystem.nonempty_recipientBoundary_of_boundaryProjection_injective
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A) (source : (x : frontier A) → C1BoundaryAt A x)
    (hinjective : Function.Injective (system.boundaryProjection A hA source))
    (hrange : range (system.boundaryProjection A hA source) =
      frontier (setValuedImage system.map system.radius A))
    (point : frontier (setValuedImage system.map system.radius A)) :
    Nonempty (C1BoundaryAt (setValuedImage system.map system.radius A) point) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by norm_num : 0 < 2) system.dimension_at_least_two)
  obtain ⟨chart⟩ := nonempty_c1FrontierGraphAt_of_sequential_normal_secants
    (system.isRegularClosed_setValuedImage A hA hcompact hregular)
    (system.recipientNormal hcontraction A hA hcompact source hinjective hrange)
    (system.continuous_recipientNormal hcontraction A hA hcompact source hinjective hrange)
    (system.norm_recipientNormal hcontraction A hA hcompact source hinjective hrange)
    (system.tendsto_recipient_secants hcontraction A hA hcompact source hinjective hrange) point
  exact ⟨chart.toC1BoundaryAt (system.isRegularClosed_setValuedImage A hA hcompact hregular)⟩

/-- Theorem 4.9: with source visibility, recipient C1 regularity is equivalent to Gamma injectivity. -/
theorem SetValuedSystem.recipientBoundary_iff_boundaryProjection_injective
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A) (source : (x : frontier A) → C1BoundaryAt A x)
    (hvisible : system.SourceVisible A) :
    (∀ point : frontier (setValuedImage system.map system.radius A),
      Nonempty (C1BoundaryAt (setValuedImage system.map system.radius A) point)) ↔
      Function.Injective (system.boundaryProjection A hA source) := by
  classical
  constructor
  · intro hrecipient
    exact (system.boundaryProjection_bijective_onto_frontier hcontraction A hA hcompact source
      (fun point => (hrecipient point).some) hvisible).1
  · intro hinjective point
    exact system.nonempty_recipientBoundary_of_boundaryProjection_injective hcontraction
      A hA hcompact hregular source hinjective
      (system.range_boundaryProjection_of_sourceVisible hcontraction A hA hcompact source hvisible) point

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The same equivalence with the manuscript's original unoriented C1 source charts. -/
theorem SetValuedSystem.recipientBoundary_iff_boundaryProjection_injective_of_frontierGraph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (hvisible : system.SourceVisible A) :
    (∀ point : frontier (setValuedImage system.map system.radius A),
      Nonempty (C1BoundaryAt (setValuedImage system.map system.radius A) point)) ↔
      Function.Injective (system.boundaryProjection A hA
        (fun x => (source x).toC1BoundaryAt hregular)) :=
  system.recipientBoundary_iff_boundaryProjection_injective hcontraction A hA hcompact
    hregular (fun x => (source x).toC1BoundaryAt hregular) hvisible

/-- Theorem 4.9 in the original frontier-graph convention, with one fixed target model. -/
theorem SetValuedSystem.recipientFrontierGraph_iff_boundaryProjection_injective
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (hvisible : system.SourceVisible A) :
    (∀ point : frontier (setValuedImage system.map system.radius A),
      Nonempty (C1FrontierGraphAt (F := Fin (Module.finrank ℝ E - 1) → ℝ)
        (setValuedImage system.map system.radius A) point)) ↔
      Function.Injective (system.boundaryProjection A hA
        (fun x => (source x).toC1BoundaryAt hregular)) := by
  classical
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by norm_num : 0 < 2) system.dimension_at_least_two)
  constructor
  · intro hrecipient
    apply (system.recipientBoundary_iff_boundaryProjection_injective_of_frontierGraph
      hcontraction A hA hcompact hregular source hvisible).mp
    intro point
    exact ⟨(hrecipient point).some.toC1BoundaryAt
      (system.isRegularClosed_setValuedImage A hA hcompact hregular)⟩
  · intro hinjective point
    have hrecipient := (system.recipientBoundary_iff_boundaryProjection_injective_of_frontierGraph
      hcontraction A hA hcompact hregular source hvisible).mpr hinjective
    exact ⟨fixedModelFrontierGraph (system.isRegularClosed_setValuedImage A hA hcompact hregular)
      (fun value => (hrecipient value).some) point⟩

end BoundedUncertainty
