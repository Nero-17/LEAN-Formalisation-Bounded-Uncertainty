import BoundedUncertainty.DualBoundaryContact
import BoundedUncertainty.NormalBundleNotation

/-!
Theorem 4.16 for the actual exponential map and the actual inward normal
bundles. The two incidence assumptions ask only for attained nearest points;
uniqueness is not needed by the proof. The hypotheses with unique nearest
points in the paper therefore imply these weaker hypotheses directly.
-/

namespace BoundedUncertainty

open Set Topology

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {r s : ℕ}

/-- The local formula identifies actual graph-based inward normal pairs. -/
theorem SetValuedSystem.exponentialMap_inwardNormalPair_of_nearest
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (A : Set E) (hregular : IsRegularClosed A)
    (hdualregular : IsRegularClosed (dualInflation system.radius A))
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (target : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (x : frontier A) (y : frontier (dualInflation system.radius A))
    (hpositive : 0 < system.radius y) (hnearest : dist (y : E) x = Metric.infDist (y : E) A) :
    exponentialMap system.radius system.radiusGradientOnAmbient
      (inwardNormalPair (dualInflation system.radius A) hdualregular target y) =
        inwardNormalPair A hregular source x := by
  have hx : (x : E) ∈ A := hregular.isClosed.frontier_subset x.property
  have hlevel := system.infDist_eq_radius_of_mem_frontier_dualInflation hwhole A
    ⟨x, hx⟩ y y.property
  exact system.exponentialMap_inward_of_dual_contact hwhole hcontraction A x y
    ((source x).toC1BoundaryAt hregular) ((target y).toC1BoundaryAt hdualregular)
    hpositive ((dist_comm (x : E) y).trans (hnearest.trans hlevel))
    (fun w hw => hlevel.symm.trans_le ((Metric.infDist_le_dist_of_mem hw).trans_eq (dist_comm _ _)))

/-- Theorem 4.16, with the paper's nearest-point assumptions weakened to attainment. -/
theorem SetValuedSystem.image_exponentialMap_inwardNormalBundle_dualInflation
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hregular : IsRegularClosed A)
    (hdualregular : IsRegularClosed (dualInflation system.radius A))
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (target : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    exponentialMap system.radius system.radiusGradientOnAmbient ''
      inwardNormalBundle (dualInflation system.radius A) hdualregular target =
        inwardNormalBundle A hregular source := by
  apply Subset.antisymm
  · rintro p ⟨q, ⟨y, rfl⟩, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hnearest y y.property
    have hlevel := system.infDist_eq_radius_of_mem_frontier_dualInflation hwhole A
      ⟨x, hx⟩ y y.property
    have hxfrontier : x ∈ frontier A := mem_frontier_of_nearest_contact A x y
      (system.radius y) hx (hpositive y) ((dist_comm x y).trans (hxy.trans hlevel))
      (fun w hw => hlevel.symm.trans_le
        ((Metric.infDist_le_dist_of_mem hw).trans_eq (dist_comm _ _)))
    exact ⟨⟨x, hxfrontier⟩, (system.exponentialMap_inwardNormalPair_of_nearest hwhole
      hcontraction A hregular hdualregular source target ⟨x, hxfrontier⟩ y (hpositive y) hxy).symm⟩
  · rintro p ⟨x, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hvisible x x.property
    refine ⟨inwardNormalPair (dualInflation system.radius A) hdualregular target ⟨y, hy⟩,
      ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    exact system.exponentialMap_inwardNormalPair_of_nearest hwhole hcontraction A
      hregular hdualregular source target x ⟨y, hy⟩ (hpositive y) hxy

/-- Compactness supplies the first incidence clause without a uniqueness assumption. -/
theorem SetValuedSystem.image_exponentialMap_inwardNormalBundle_dualInflation_of_compact
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hcompact : IsCompact A) (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (target : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    exponentialMap system.radius system.radiusGradientOnAmbient ''
      inwardNormalBundle (dualInflation system.radius A)
        (system.isRegularClosed_dualInflation hwhole hcontraction hpositive A hcompact) target =
      inwardNormalBundle A hregular source := by
  apply system.image_exponentialMap_inwardNormalBundle_dualInflation hwhole hcontraction
    hpositive A hregular _ source target ?_ hvisible
  intro y hy
  rcases A.eq_empty_or_nonempty with hempty | hnonempty
  · simp only [hempty, dualInflation_empty, frontier_empty, mem_empty_iff_false] at hy
  · obtain ⟨x, hx, hdist⟩ := hcompact.exists_infDist_eq_dist hnonempty y
    exact ⟨x, hx, hdist.symm⟩

end BoundedUncertainty
