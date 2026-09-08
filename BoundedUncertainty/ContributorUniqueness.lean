import BoundedUncertainty.C1FrontierContact
import BoundedUncertainty.Section3Interfaces
import BoundedUncertainty.ExponentialInjectivity

/-!
# Unique contributors at smooth recipient boundaries

Lemma 4.4 does not assume any source-boundary regularity. The recipient's
outward normal places every contributing center on the same admissible ray.
This includes zero radius, when the position equation is independent of the
normal. Strict monotonicity along the ray then identifies the centers.
Compactness is used only to establish existence, not in the uniqueness step.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- At a smooth recipient, all admissible contributing centers coincide. -/
theorem SetValuedSystem.contributor_eq_of_recipient_boundary
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain)
    (hballs : ∀ y ∈ B, Metric.closedBall y (system.radius y) ⊆ system.domain)
    (y₁ y₂ z : E) (recipient : C1BoundaryAt (inflation system.radius B) z)
    (hy₁ : y₁ ∈ B) (hy₂ : y₂ ∈ B)
    (hcontact₁ : dist z y₁ = system.radius y₁)
    (hcontact₂ : dist z y₂ = system.radius y₂) : y₁ = y₂ := by
  have hposition₁ := recipient.position_eq_of_inflation_contact system.radius B y₁ z
    hy₁ (system.radius_nonneg y₁ (hB hy₁)) hcontact₁
  have hposition₂ := recipient.position_eq_of_inflation_contact system.radius B y₂ z
    hy₂ (system.radius_nonneg y₂ (hB hy₂)) hcontact₂
  have hroot₁ : z - system.radius y₁ • recipient.normal = y₁ := by
    exact sub_eq_iff_eq_add.mpr hposition₁
  have hroot₂ : z - system.radius y₂ • recipient.normal = y₂ := by
    exact sub_eq_iff_eq_add.mpr hposition₂
  have hradius := system.radius_eq_of_ray_roots hcontraction y₁ y₂ z recipient.normal
    (hB hy₁) (hB hy₂) (hballs y₁ hy₁) (hballs y₂ hy₂)
    recipient.normal_unit hroot₁ hroot₂
  exact hroot₁.symm.trans ((congrArg (fun radius : ℝ => z - radius • recipient.normal) hradius).trans hroot₂)

/-- The uniqueness statement uses the paper's actual constituent-frontier relation. -/
theorem SetValuedSystem.contributor_eq_of_contributingPairs
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain)
    (hballs : ∀ y ∈ B, Metric.closedBall y (system.radius y) ⊆ system.domain)
    (y₁ y₂ z : E) (recipient : C1BoundaryAt (inflation system.radius B) z)
    (hfirst : IsContributingPair system.radius B y₁ z)
    (hsecond : IsContributingPair system.radius B y₂ z) : y₁ = y₂ :=
  system.contributor_eq_of_recipient_boundary hcontraction B hB hballs y₁ y₂ z recipient
    hfirst.1 hsecond.1
    (Metric.frontier_closedBall_subset_sphere hfirst.2.2)
    (Metric.frontier_closedBall_subset_sphere hsecond.2.2)

/-- A contributing pair at a smooth recipient is unique in the sense of Notation 3.3. -/
theorem SetValuedSystem.isUniqueContributingPair_of_recipient_boundary
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain)
    (hballs : ∀ y ∈ B, Metric.closedBall y (system.radius y) ⊆ system.domain)
    (y z : E) (recipient : C1BoundaryAt (inflation system.radius B) z)
    (hpair : IsContributingPair system.radius B y z) :
    IsUniqueContributingPair system.radius B y z := by
  refine ⟨hpair, ?_⟩
  intro other _ hother
  exact system.contributor_eq_of_contributingPairs hcontraction B hB hballs other y z
    recipient hother hpair

/-- Lemma 4.4: compactness supplies a contributor, and it lies on the source frontier. -/
theorem SetValuedSystem.exists_unique_contributor_of_compact
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (hcompact : IsCompact B)
    (hballs : ∀ y ∈ B, Metric.closedBall y (system.radius y) ⊆ system.domain)
    (z : E) (recipient : C1BoundaryAt (inflation system.radius B) z) :
    ∃! y : E, y ∈ frontier B ∧ IsContributingPair system.radius B y z := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  obtain ⟨y, hy, hcontact⟩ := exists_mem_sphere_of_mem_frontier_inflation
    system.radius B hcompact (system.radius_extension.continuousOn.mono hB)
    (fun w hw => system.radius_nonneg w (hB hw)) z recipient.mem_frontier
  have hpair : IsContributingPair system.radius B y z :=
    ⟨hy, recipient.mem_frontier, (system.mem_frontier_constituent_iff_dist y z).mpr hcontact⟩
  refine ⟨y, ⟨system.contributor_mem_frontier hcontraction B hB y z hy
    recipient.mem_frontier hcontact, hpair⟩, ?_⟩
  intro other hother
  exact system.contributor_eq_of_contributingPairs hcontraction B hB hballs other y z
    recipient hother.2 hpair

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The original unoriented frontier-chart convention also gives existence and uniqueness. -/
theorem SetValuedSystem.exists_unique_contributor_of_frontierGraph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (hcompact : IsCompact B)
    (hregular : IsRegularClosed B)
    (hballs : ∀ y ∈ B, Metric.closedBall y (system.radius y) ⊆ system.domain)
    (z : E) (recipient : C1FrontierGraphAt (F := F) (inflation system.radius B) z) :
    ∃! y : E, y ∈ frontier B ∧ IsContributingPair system.radius B y z :=
  system.exists_unique_contributor_of_compact hcontraction B hB hcompact hballs z
    (recipient.toC1BoundaryAt (system.isRegularClosed_inflation_of_compact B hB hcompact hregular))

/-- The full existence-and-uniqueness statement for the actual one-step set-valued image. -/
theorem SetValuedSystem.exists_unique_contributor_setValuedImage
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (z : E) (recipient : C1BoundaryAt (setValuedImage system.map system.radius A) z) :
    ∃! y : E, y ∈ frontier (system.map '' A) ∧
      IsContributingPair system.radius (system.map '' A) y z := by
  rw [setValuedImage_eq_inflation] at recipient
  apply system.exists_unique_contributor_of_compact hcontraction (system.map '' A) _
    (hcompact.image_of_continuousOn (system.diffeomorphism.forward_extension.continuousOn.mono hA))
    _ z recipient
  · rintro _ ⟨x, hx, rfl⟩
    exact system.map_into_domain (hA hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact system.ball_into_domain x (hA hx)

end BoundedUncertainty
