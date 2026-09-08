import BoundedUncertainty.ForwardBoundaryCorrespondence
import BoundedUncertainty.RecipientUniqueness
import BoundedUncertainty.HigherBoundaryInverse

/-! The forward correspondence in the manuscript's unoriented frontier-chart convention. -/

namespace BoundedUncertainty

open Set

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {r s : ℕ}

/-- Changing an equal set preserves the actual defining function and normal. -/
def C1BoundaryAt.onSetEquality {A B : Set E} {x : E}
    (boundary : C1BoundaryAt A x) (heq : A = B) : C1BoundaryAt B x :=
  { boundary with
    mem_iff := by
      intro z hz
      rw [← heq]
      exact boundary.mem_iff z hz }

/-- The source assumptions imply regular closedness of the one-step image. -/
theorem SetValuedSystem.isRegularClosed_setValuedImage
    (system : SetValuedSystem (E := E) r s) (A : Set E)
    (hA : A ⊆ system.domain) (hcompact : IsCompact A) (hregular : IsRegularClosed A) :
    IsRegularClosed (setValuedImage system.map system.radius A) := by
  rw [setValuedImage_eq_inflation]
  apply system.isRegularClosed_inflation_of_compact (system.map '' A) _
    (system.diffeomorphism.isCompact_image hA hcompact)
    (system.diffeomorphism.isRegularClosed_image system.map_order_pos hA hcompact hregular)
  rintro y ⟨x, hx, rfl⟩
  exact system.map_into_domain (hA hx)

/-- Lemma 4.2 starts from a source chart at x; no image chart is an extra assumption. -/
theorem SetValuedSystem.recipient_eq_of_source_frontierGraph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A) (x z₁ z₂ : E)
    (source : C1FrontierGraphAt (F := F) A x)
    (hfirst : IsContributingPair system.radius (system.map '' A) (system.map x) z₁)
    (hsecond : IsContributingPair system.radius (system.map '' A) (system.map x) z₂) :
    z₁ = z₂ := by
  obtain ⟨imageBoundary, _⟩ := system.exists_imageBoundary_of_frontierGraph
    A hA hcompact hregular x source
  apply system.recipient_eq_of_contributingPairs hcontraction (system.map '' A) _
    (system.map x) z₁ z₂ imageBoundary hfirst hsecond
  rintro y ⟨a, ha, rfl⟩
  exact system.map_into_domain (hA ha)

/-- Corollary 4.3 under the original source-boundary hypotheses. -/
theorem SetValuedSystem.single_noise_sphere_subsingleton_of_source_frontierGraph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A) (x : E)
    (source : C1FrontierGraphAt (F := F) A x) :
    (frontier (Metric.closedBall (system.map x) (system.radius (system.map x))) ∩
      frontier (setValuedImage system.map system.radius A)).Subsingleton := by
  obtain ⟨imageBoundary, _⟩ := system.exists_imageBoundary_of_frontierGraph
    A hA hcompact hregular x source
  exact system.constituent_frontier_inter_frontier_setValuedImage_subsingleton
    hcontraction A hA (system.map x) imageBoundary

/-- Theorem 4.6, with the normal bundles already defined in Notation 3.3. -/
theorem SetValuedSystem.image_outwardNormalBundle
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (recipient : (z : frontier (setValuedImage system.map system.radius A)) →
      C1FrontierGraphAt (F := G) (setValuedImage system.map system.radius A) z)
    (hvisible : system.SourceVisible A) :
    system.boundaryFormulaOnAmbient '' outwardNormalBundle A hregular source =
      outwardNormalBundle (setValuedImage system.map system.radius A)
        (system.isRegularClosed_setValuedImage A hA hcompact hregular) recipient := by
  calc
    _ = range (fun x => system.boundaryFormula
        (system.boundaryNormalInput A hA (fun x => (source x).toC1BoundaryAt hregular) x)) := by
      rw [outwardNormalBundle, ← range_comp]
      congr 1
      funext x
      exact system.boundaryFormulaOnAmbient_apply
        (system.boundaryNormalInput A hA (fun x => (source x).toC1BoundaryAt hregular) x)
    _ = _ := system.boundaryFormula_normalInput_range hcontraction A hA hcompact
      (fun x => (source x).toC1BoundaryAt hregular)
      (fun z => (recipient z).toC1BoundaryAt
        (system.isRegularClosed_setValuedImage A hA hcompact hregular)) hvisible

/-- Corollary 4.7: an invariant set with source visibility has an invariant outward bundle. -/
theorem SetValuedSystem.image_outwardNormalBundle_of_invariant
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (M : Set E) (hM : M ⊆ system.domain) (hcompact : IsCompact M)
    (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hvisible : system.SourceVisible M)
    (hinvariant : setValuedImage system.map system.radius M = M) :
    system.boundaryFormulaOnAmbient '' outwardNormalBundle M hregular boundary =
      outwardNormalBundle M hregular boundary := by
  have hcontactFormula (x z : frontier M)
      (hcontact : IsContributingPair system.radius (system.map '' M) (system.map x) z) :
      system.boundaryFormulaOnAmbient (outwardNormalPair M hregular boundary x) =
        outwardNormalPair M hregular boundary z := by
    exact (system.boundaryFormulaOnAmbient_apply
      (system.boundaryNormalInput M hM (fun x => (boundary x).toC1BoundaryAt hregular) x)).trans
      (system.boundaryFormula_of_contributingPair hcontraction M hM hcompact x z
      ((boundary x).toC1BoundaryAt hregular)
      (((boundary z).toC1BoundaryAt hregular).onSetEquality hinvariant.symm) hcontact)
  apply Set.Subset.antisymm
  · rintro p ⟨q, ⟨x, rfl⟩, rfl⟩
    obtain ⟨z, hcontact⟩ := (system.sourceVisible_iff_contributingPair M hcompact.isClosed).mp
      hvisible x x.property
    have hz : z ∈ frontier M := by
      rw [← hinvariant, setValuedImage_eq_inflation]
      exact hcontact.2.1
    exact ⟨⟨z, hz⟩, (hcontactFormula x ⟨z, hz⟩ hcontact).symm⟩
  · rintro p ⟨z, rfl⟩
    have hz : (z : E) ∈ frontier (setValuedImage system.map system.radius M) := by
      rw [hinvariant]
      exact z.property
    obtain ⟨x, hx, hcontact⟩ := system.exists_source_frontier_contributingPair
      hcontraction M hM hcompact z hz
    exact ⟨outwardNormalPair M hregular boundary ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩,
      hcontactFormula ⟨x, hx⟩ z hcontact⟩

end BoundedUncertainty
