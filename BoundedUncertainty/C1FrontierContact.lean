import BoundedUncertainty.C1FrontierGraph
import BoundedUncertainty.ContributorFormula
import BoundedUncertainty.InflationGeometry

/-!
Lemmas 3.5--3.7 and Theorem 3.8 with the original unoriented C1 frontier
graph hypotheses. Regular closedness supplies the domain side. Contact is
stated on the frontier of the constituent closed ball, including radius zero.
-/

namespace BoundedUncertainty

open Set Topology

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The outward normal obtained from an unoriented frontier graph of a regular closed set. -/
noncomputable def C1FrontierGraphAt.outwardNormal {B : Set E} {y : E}
    (chart : C1FrontierGraphAt (F := F) B y) (hB : IsRegularClosed B) : E :=
  (chart.toC1BoundaryAt hB).normal

theorem C1FrontierGraphAt.norm_outwardNormal {B : Set E} {y : E}
    (chart : C1FrontierGraphAt (F := F) B y) (hB : IsRegularClosed B) :
    ‖chart.outwardNormal hB‖ = 1 := (chart.toC1BoundaryAt hB).normal_unit

/-- Lemma 3.5: inclusion determines the same outward normal at a common smooth frontier point. -/
theorem C1FrontierGraphAt.outwardNormal_eq_of_subset {B C : Set E} {y : E}
    (source : C1FrontierGraphAt (F := F) B y) (recipient : C1FrontierGraphAt (F := G) C y)
    (hB : IsRegularClosed B) (hC : IsRegularClosed C) (hBC : B ⊆ C) :
    source.outwardNormal hB = recipient.outwardNormal hC :=
  (source.toC1BoundaryAt hB).normal_eq_of_subset (recipient.toC1BoundaryAt hC) hBC

/-- In particular, the normal is independent of the chosen graph chart. -/
theorem C1FrontierGraphAt.outwardNormal_unique {B : Set E} {y : E}
    (first : C1FrontierGraphAt (F := F) B y) (second : C1FrontierGraphAt (F := G) B y)
    (hB : IsRegularClosed B) : first.outwardNormal hB = second.outwardNormal hB :=
  first.outwardNormal_eq_of_subset second hB hB Set.Subset.rfl

/-- Lemma 3.6 for the actual constituent-ball frontier contact relation. -/
theorem C1FrontierGraphAt.outwardNormal_eq_radial_of_contact (radius : E → ℝ)
    (B : Set E) (y z : E) (recipient : C1FrontierGraphAt (F := F) (inflation radius B) z)
    (hregular : IsRegularClosed (inflation radius B)) (hy : y ∈ B)
    (hpositive : 0 < radius y) (hcontact : z ∈ frontier (Metric.closedBall y (radius y))) :
    recipient.outwardNormal hregular = ‖z - y‖⁻¹ • (z - y) :=
  (recipient.toC1BoundaryAt hregular).normal_eq_radial_of_inflation_contact
    radius B y z hy hpositive (Metric.frontier_closedBall_subset_sphere hcontact)

variable {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.isRegularClosed_inflation_of_compact
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (hcompact : IsCompact B) (hregular : IsRegularClosed B) :
    IsRegularClosed (inflation system.radius B) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  exact isRegularClosed_inflation system.radius B hcompact hregular
    (system.radius_extension.continuousOn.mono hB)
    (fun y hy => system.radius_nonneg y (hB hy))

omit [CompleteSpace E] in
/-- The paper's contributor contact and the distance equation agree, including radius zero. -/
theorem SetValuedSystem.mem_frontier_constituent_iff_dist
    (system : SetValuedSystem (E := E) r s) (y z : E) :
    z ∈ frontier (Metric.closedBall y (system.radius y)) ↔ dist z y = system.radius y := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  rw [frontier_closedBall']
  rfl

/-- Lemma 3.7 now assumes only a C1 hypersurface frontier, with its side derived. -/
theorem SetValuedSystem.exists_nonneg_contact_multiplier_of_frontierGraph
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (hregular : IsRegularClosed B) (y z : E) (source : C1FrontierGraphAt (F := F) B y)
    (hz : z ∈ frontier (inflation system.radius B))
    (hcontact : z ∈ frontier (Metric.closedBall y (system.radius y))) :
    ∃ coefficient : ℝ, 0 ≤ coefficient ∧
      system.contactGradient z y = (-2 * coefficient) • source.outwardNormal hregular :=
  system.exists_nonneg_contact_multiplier B hB y z (source.toC1BoundaryAt hregular) hz
    (Metric.frontier_closedBall_subset_sphere hcontact)

/-- Theorem 3.8 on the genuine normal bundle under the original frontier graph assumptions. -/
theorem SetValuedSystem.exponentialLift_of_frontierGraph_contact
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (hcompact : IsCompact B)
    (hregular : IsRegularClosed B) (y z : E)
    (source : C1FrontierGraphAt (F := F) B y)
    (recipient : C1FrontierGraphAt (F := G) (inflation system.radius B) z)
    (hcontact : z ∈ frontier (Metric.closedBall y (system.radius y))) :
    system.exponentialLift hcontraction
      (⟨y, hB (source.toC1BoundaryAt hregular).mem⟩,
        ⟨source.outwardNormal hregular, source.norm_outwardNormal hregular⟩) =
      (z, ⟨recipient.outwardNormal
          (system.isRegularClosed_inflation_of_compact B hB hcompact hregular),
        recipient.norm_outwardNormal
          (system.isRegularClosed_inflation_of_compact B hB hcompact hregular)⟩) :=
  system.exponentialLift_of_inflation_contact hcontraction B hB y z
    (source.toC1BoundaryAt hregular)
    (recipient.toC1BoundaryAt (system.isRegularClosed_inflation_of_compact B hB hcompact hregular))
    (Metric.frontier_closedBall_subset_sphere hcontact)

/-- The explicit nonnegative-root multiplier formula of Theorem 3.8. -/
theorem SetValuedSystem.contact_position_eq_explicit_multiplier_of_frontierGraph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (hcompact : IsCompact B)
    (hregular : IsRegularClosed B) (y z : E)
    (source : C1FrontierGraphAt (F := F) B y)
    (recipient : C1FrontierGraphAt (F := G) (inflation system.radius B) z)
    (hcontact : z ∈ frontier (Metric.closedBall y (system.radius y))) :
    z = y + (system.radius y *
      (inner ℝ (source.outwardNormal hregular) (system.radiusGradientOnAmbient y) +
        Real.sqrt ((inner ℝ (source.outwardNormal hregular)
          (system.radiusGradientOnAmbient y)) ^ 2 -
            ‖system.radiusGradientOnAmbient y‖ ^ 2 + 1))) • source.outwardNormal hregular -
      system.radius y • system.radiusGradientOnAmbient y :=
  system.contact_position_eq_explicit_multiplier hcontraction B hB y z
    (source.toC1BoundaryAt hregular)
    (recipient.toC1BoundaryAt (system.isRegularClosed_inflation_of_compact B hB hcompact hregular))
    (Metric.frontier_closedBall_subset_sphere hcontact)

end BoundedUncertainty
