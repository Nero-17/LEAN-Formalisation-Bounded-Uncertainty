import BoundedUncertainty.C1FrontierContact
import BoundedUncertainty.Section3Interfaces

/-!
# Unique recipients of smooth contributing centers

Lemma 4.2 uses smoothness only at the contributing center. No regularity of
the recipient boundary is assumed. The signed contact multiplier determines
the recipient position, including at zero radius. Corollary 4.3 is expressed
as a subsingleton intersection of the actual constituent-ball frontier with
the inflation frontier.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- The contact position is determined by the source normal alone. -/
theorem SetValuedSystem.recipient_position_eq_normalUpdate
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z : E) (source : C1BoundaryAt B y)
    (hz : z ∈ frontier (inflation system.radius B))
    (hcontact : dist z y = system.radius y) :
    z = y + system.radius y • normalUpdate (system.radiusGradientOnAmbient y) source.normal := by
  by_cases hzero : system.radius y = 0
  · have hzy : z = y := dist_eq_zero.mp (hcontact.trans hzero)
    simpa only [hzero, zero_smul, add_zero] using hzy
  · have hpositive : 0 < system.radius y :=
      lt_of_le_of_ne (system.radius_nonneg y (hB source.mem)) (Ne.symm hzero)
    have hnorm : ‖z - y‖ = system.radius y := by
      simpa only [dist_eq_norm] using hcontact
    have hnonzero : z - y ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne hzero)
    have hscaled : system.radius y • (‖z - y‖⁻¹ • (z - y)) = z - y := by
      rw [smul_smul, hnorm, mul_inv_cancel₀ hzero, one_smul]
    obtain ⟨coefficient, hnonneg, hmultiplier⟩ :=
      system.exists_nonneg_contact_position_multiplier B hB y z source hz hcontact
    have hnormal := normalUpdate_eq_of_nonneg_scaled_contact
      (system.radiusGradientOnAmbient y) source.normal (‖z - y‖⁻¹ • (z - y))
      (hcontraction.norm_radiusGradientOnAmbient y (hB source.mem))
      source.normal_unit (norm_smul_inv_norm hnonzero)
      (system.radius y) coefficient hpositive hnonneg (by
        rw [hscaled]
        exact hmultiplier)
    rw [hnormal, hscaled]
    abel

/-- Lemma 4.2: two actual recipients of the same smooth center coincide. -/
theorem SetValuedSystem.recipient_eq_of_contributingPairs
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z₁ z₂ : E) (source : C1BoundaryAt B y)
    (hfirst : IsContributingPair system.radius B y z₁)
    (hsecond : IsContributingPair system.radius B y z₂) : z₁ = z₂ :=
  (system.recipient_position_eq_normalUpdate hcontraction B hB y z₁ source hfirst.2.1
    (Metric.frontier_closedBall_subset_sphere hfirst.2.2)).trans
      (system.recipient_position_eq_normalUpdate hcontraction B hB y z₂ source hsecond.2.1
        (Metric.frontier_closedBall_subset_sphere hsecond.2.2)).symm

/-- Corollary 4.3: the relevant part of a single noise sphere has at most one point. -/
theorem SetValuedSystem.constituent_frontier_inter_frontier_inflation_subsingleton
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y : E) (source : C1BoundaryAt B y) :
    (frontier (Metric.closedBall y (system.radius y)) ∩
      frontier (inflation system.radius B)).Subsingleton := by
  intro z₁ hz₁ z₂ hz₂
  exact system.recipient_eq_of_contributingPairs hcontraction B hB y z₁ z₂ source
    ⟨source.mem, hz₁.2, hz₁.1⟩ ⟨source.mem, hz₂.2, hz₂.1⟩

/-- Any parameterized arc contained in that intersection is constant. -/
theorem SetValuedSystem.eq_of_mem_single_noise_sphere_arc
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y : E) (source : C1BoundaryAt B y)
    {P : Type*} (arc : P → E) (parameters : Set P)
    (harc : MapsTo arc parameters
      (frontier (Metric.closedBall y (system.radius y)) ∩ frontier (inflation system.radius B)))
    (a b : P) (ha : a ∈ parameters) (hb : b ∈ parameters) : arc a = arc b :=
  system.constituent_frontier_inter_frontier_inflation_subsingleton hcontraction B hB y source
    (harc ha) (harc hb)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The same uniqueness with the unoriented C1 frontier-chart convention. -/
theorem SetValuedSystem.recipient_eq_of_frontierGraph_contributingPairs
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (hregular : IsRegularClosed B)
    (y z₁ z₂ : E) (source : C1FrontierGraphAt (F := F) B y)
    (hfirst : IsContributingPair system.radius B y z₁)
    (hsecond : IsContributingPair system.radius B y z₂) : z₁ = z₂ :=
  system.recipient_eq_of_contributingPairs hcontraction B hB y z₁ z₂
    (source.toC1BoundaryAt hregular) hfirst hsecond

/-- Corollary 4.3 for the actual set-valued image, assuming boundary data at the center. -/
theorem SetValuedSystem.constituent_frontier_inter_frontier_setValuedImage_subsingleton
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (y : E)
    (source : C1BoundaryAt (system.map '' A) y) :
    (frontier (Metric.closedBall y (system.radius y)) ∩
      frontier (setValuedImage system.map system.radius A)).Subsingleton := by
  rw [setValuedImage_eq_inflation]
  apply system.constituent_frontier_inter_frontier_inflation_subsingleton hcontraction
    (system.map '' A) _ y source
  rintro _ ⟨x, hx, rfl⟩
  exact system.map_into_domain (hA hx)

end BoundedUncertainty
