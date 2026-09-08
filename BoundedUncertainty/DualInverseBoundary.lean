import BoundedUncertainty.DualBoundaryCorrespondence
import BoundedUncertainty.WholeSpaceNormalTransport

/-!
Theorem 4.17: the actual inverse boundary map sends the inward normal bundle
of the original set onto that of its actual union-defined dual set map.
The deterministic transport is proved through actual preimage defining data.
The bundle statement is independent of the chosen valid frontier charts.
-/

namespace BoundedUncertainty

open Set Topology

variable {E F G H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {r s : ℕ}

/-- C1 boundary data for the actual dual set map follow from the dual-inflation boundary data. -/
theorem SetValuedSystem.exists_C1BoundaryAt_dualSetMap
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) (A : Set E)
    (target : (y : frontier (dualInflation system.radius A)) →
      C1BoundaryAt (dualInflation system.radius A) y)
    (x : E) (hx : x ∈ frontier (dualSetMap system.map system.radius A)) :
    Nonempty (C1BoundaryAt (dualSetMap system.map system.radius A) x) := by
  rw [dualSetMap_eq_preimage] at hx ⊢
  have htarget : system.map x ∈ frontier (dualInflation system.radius A) := by
    rw [system.frontier_preimage_of_wholeSpace hwhole hself] at hx
    exact hx
  obtain ⟨source, _⟩ := system.exists_preimageBoundary_of_wholeSpace hwhole
    (dualInflation system.radius A) x (target ⟨system.map x, htarget⟩)
  exact ⟨source⟩

/-- Theorem 4.17 for any valid choices of the actual frontier charts. -/
theorem SetValuedSystem.image_boundaryInverseOnAmbient_inwardNormalBundle_dualSetMap
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hregular : IsRegularClosed A)
    (hdualregular : IsRegularClosed (dualInflation system.radius A))
    (hdualsetregular : IsRegularClosed (dualSetMap system.map system.radius A))
    (original : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (inflated : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (source : (x : frontier (dualSetMap system.map system.radius A)) →
      C1FrontierGraphAt (F := H) (dualSetMap system.map system.radius A) x)
    (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    system.boundaryInverseOnAmbient hcontraction '' inwardNormalBundle A hregular original =
      inwardNormalBundle (dualSetMap system.map system.radius A) hdualsetregular source := by
  revert source hdualsetregular
  rw [dualSetMap_eq_preimage]
  intro hdualsetregular source
  have hlinear := system.image_linearLiftOnAmbient_inwardNormalBundle_preimage hwhole hself
    (dualInflation system.radius A) hdualregular hdualsetregular inflated source
  have hexponential := system.image_exponentialMap_inwardNormalBundle_dualInflation hwhole
    hcontraction hpositive A hregular hdualregular original inflated hnearest hvisible
  have hbeta : system.boundaryFormulaOnAmbient ''
      inwardNormalBundle (system.map ⁻¹' dualInflation system.radius A) hdualsetregular source =
        inwardNormalBundle A hregular original := by
    rw [SetValuedSystem.boundaryFormulaOnAmbient, image_comp, hlinear, hexponential]
  have hleft : LeftInvOn (system.boundaryInverseOnAmbient hcontraction)
      system.boundaryFormulaOnAmbient
        (inwardNormalBundle (system.map ⁻¹' dualInflation system.radius A) hdualsetregular source) := by
    intro p hp
    have hnormal := (inwardNormalBundle_subset _ hdualsetregular source hp).2
    rw [system.boundaryFormulaOnAmbient_apply
      (⟨p.1, hwhole ▸ mem_univ p.1⟩, ⟨p.2, hnormal⟩)]
    exact system.boundaryInverseOnAmbient_formula hcontraction
      (⟨p.1, hwhole ▸ mem_univ p.1⟩, ⟨p.2, hnormal⟩)
  rw [← hbeta]
  exact hleft.image_image

end BoundedUncertainty
