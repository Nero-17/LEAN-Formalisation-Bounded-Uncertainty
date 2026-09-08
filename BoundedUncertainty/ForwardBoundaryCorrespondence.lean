import BoundedUncertainty.SourceVisibility
import BoundedUncertainty.DiffeomorphismBoundaryNormal
import BoundedUncertainty.NormalBundleNotation
import BoundedUncertainty.ContractionCharacterization

/-! Local normal transport and forward boundary correspondence (Lemmas 4.5–4.7). -/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {r s : ℕ}

/-- Lemma 4.5 for the actual derivative, gradient, and contributing pair.
The proof also covers zero radius. -/
theorem SetValuedSystem.boundaryFormula_of_contributingPair
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (x z : E) (source : C1BoundaryAt A x)
    (recipient : C1BoundaryAt (setValuedImage system.map system.radius A) z)
    (hcontact : IsContributingPair system.radius (system.map '' A) (system.map x) z) :
    system.boundaryFormula (⟨x, hA source.mem⟩, ⟨source.normal, source.normal_unit⟩) =
      (z, recipient.normal) := by
  obtain ⟨imageBoundary, hnormal⟩ := system.exists_imageBoundary A hA hcompact x source
  have himage : system.map '' A ⊆ system.domain := by
    rintro y ⟨a, ha, rfl⟩
    exact system.map_into_domain (hA ha)
  have hpair :
      (((system.linearLift (⟨x, hA source.mem⟩, ⟨source.normal, source.normal_unit⟩)).1 : E),
       ((system.linearLift (⟨x, hA source.mem⟩, ⟨source.normal, source.normal_unit⟩)).2 : E)) =
      (system.map x, imageBoundary.normal) := Prod.ext rfl hnormal.symm
  unfold SetValuedSystem.boundaryFormula
  rw [hpair]
  let recipientInflation : C1BoundaryAt (inflation system.radius (system.map '' A)) z :=
    { recipient with
      mem_iff := by
        intro w hw
        rw [← setValuedImage_eq_inflation]
        exact recipient.mem_iff w hw }
  exact system.exponentialMap_of_inflation_contact hcontraction (system.map '' A) himage
    (system.map x) z imageBoundary recipientInflation
    (Metric.frontier_closedBall_subset_sphere hcontact.2.2)

/-- A source outward normal pair regarded as an input to the system's boundary map. -/
noncomputable def SetValuedSystem.boundaryNormalInput
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (boundary : (x : frontier A) → C1BoundaryAt A x) (x : frontier A) :
    system.domain × {n : E // ‖n‖ = 1} :=
  (⟨x, hA (boundary x).mem⟩, ⟨(boundary x).normal, (boundary x).normal_unit⟩)

theorem SetValuedSystem.boundaryNormalInput_injective
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (boundary : (x : frontier A) → C1BoundaryAt A x) :
    Function.Injective (system.boundaryNormalInput A hA boundary) := by
  intro x y h
  exact Subtype.ext (congrArg (fun p : system.domain × {n : E // ‖n‖ = 1} => (p.1 : E)) h)

/-- Visibility ensures that the computed pair is the actual recipient normal pair. -/
theorem SetValuedSystem.boundaryFormula_normalInput_mem_range
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (recipient : (z : frontier (setValuedImage system.map system.radius A)) →
      C1BoundaryAt (setValuedImage system.map system.radius A) z)
    (hvisible : system.SourceVisible A) (x : frontier A) :
    system.boundaryFormula (system.boundaryNormalInput A hA source x) ∈
      range (fun z : frontier (setValuedImage system.map system.radius A) =>
        ((z : E), (recipient z).normal)) := by
  obtain ⟨z, hcontact⟩ :=
    (system.sourceVisible_iff_contributingPair A hcompact.isClosed).mp hvisible x x.property
  have hz : z ∈ frontier (setValuedImage system.map system.radius A) := by
    simpa only [setValuedImage_eq_inflation] using hcontact.2.1
  exact ⟨⟨z, hz⟩, (system.boundaryFormula_of_contributingPair hcontraction A hA hcompact
    x z (source x) (recipient ⟨z, hz⟩) hcontact).symm⟩

/-- Theorem 4.6: the image of the source normal pairs is precisely the target normal bundle. -/
theorem SetValuedSystem.boundaryFormula_normalInput_range
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (recipient : (z : frontier (setValuedImage system.map system.radius A)) →
      C1BoundaryAt (setValuedImage system.map system.radius A) z)
    (hvisible : system.SourceVisible A) :
    range (fun x => system.boundaryFormula (system.boundaryNormalInput A hA source x)) =
      range (fun z : frontier (setValuedImage system.map system.radius A) =>
        ((z : E), (recipient z).normal)) := by
  apply Set.Subset.antisymm
  · rintro p ⟨x, rfl⟩
    exact system.boundaryFormula_normalInput_mem_range hcontraction A hA hcompact
      source recipient hvisible x
  · rintro p ⟨z, rfl⟩
    obtain ⟨x, hx, hcontact⟩ := system.exists_source_frontier_contributingPair
      hcontraction A hA hcompact z z.property
    exact ⟨⟨x, hx⟩, system.boundaryFormula_of_contributingPair hcontraction A hA hcompact
      x z (source ⟨x, hx⟩) (recipient z) hcontact⟩

/-- The actual first coordinate of beta lies on the recipient boundary. -/
theorem SetValuedSystem.boundaryFormula_normalInput_position_mem_frontier
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (recipient : (z : frontier (setValuedImage system.map system.radius A)) →
      C1BoundaryAt (setValuedImage system.map system.radius A) z)
    (hvisible : system.SourceVisible A) (x : frontier A) :
    (system.boundaryFormula (system.boundaryNormalInput A hA source x)).1 ∈
      frontier (setValuedImage system.map system.radius A) := by
  obtain ⟨z, hz⟩ := system.boundaryFormula_normalInput_mem_range hcontraction A hA hcompact
    source recipient hvisible x
  exact (congrArg Prod.fst hz) ▸ z.property

/-- The projected boundary map with its proved boundary codomain. -/
noncomputable def SetValuedSystem.projectedBoundaryMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (recipient : (z : frontier (setValuedImage system.map system.radius A)) →
      C1BoundaryAt (setValuedImage system.map system.radius A) z)
    (hvisible : system.SourceVisible A) :
    frontier A → frontier (setValuedImage system.map system.radius A) :=
  fun x => ⟨(system.boundaryFormula (system.boundaryNormalInput A hA source x)).1,
    system.boundaryFormula_normalInput_position_mem_frontier hcontraction A hA hcompact
      source recipient hvisible x⟩

/-- The projected boundary map in Theorem 4.6 is a bijection. -/
theorem SetValuedSystem.projectedBoundaryMap_bijective
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (recipient : (z : frontier (setValuedImage system.map system.radius A)) →
      C1BoundaryAt (setValuedImage system.map system.radius A) z)
    (hvisible : system.SourceVisible A) :
    Function.Bijective (system.projectedBoundaryMap hcontraction A hA hcompact
      source recipient hvisible) := by
  constructor
  · intro x y hxy
    obtain ⟨z, hz⟩ := system.boundaryFormula_normalInput_mem_range hcontraction A hA hcompact
      source recipient hvisible x
    obtain ⟨w, hw⟩ := system.boundaryFormula_normalInput_mem_range hcontraction A hA hcompact
      source recipient hvisible y
    have hzw : z = w := Subtype.ext ((congrArg Prod.fst hz).trans
      ((congrArg Subtype.val hxy).trans (congrArg Prod.fst hw).symm))
    have hpairs : system.boundaryFormula (system.boundaryNormalInput A hA source x) =
        system.boundaryFormula (system.boundaryNormalInput A hA source y) := by
      rw [← hz, ← hw, hzw]
    rw [system.boundaryFormula_eq_boundaryMap hcontraction,
      system.boundaryFormula_eq_boundaryMap hcontraction] at hpairs
    have hbeta : system.boundaryMap hcontraction (system.boundaryNormalInput A hA source x) =
        system.boundaryMap hcontraction (system.boundaryNormalInput A hA source y) :=
      Prod.ext (Subtype.ext (congrArg (fun p : E × E => p.1) hpairs))
        (Subtype.ext (congrArg (fun p : E × E => p.2) hpairs))
    exact system.boundaryNormalInput_injective A hA source
      (system.boundaryMap_injective hcontraction hbeta)
  · intro z
    obtain ⟨x, hx, hcontact⟩ := system.exists_source_frontier_contributingPair
      hcontraction A hA hcompact z z.property
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    exact congrArg Prod.fst (system.boundaryFormula_of_contributingPair
      hcontraction A hA hcompact x z (source ⟨x, hx⟩) (recipient z) hcontact)

end BoundedUncertainty
