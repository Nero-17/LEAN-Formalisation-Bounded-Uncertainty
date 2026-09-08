import BoundedUncertainty.BoundaryContinuity
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.IntermediateValue

/-!
# Surjectivity when the deterministic map has full image

When `f(X) = X`, every constituent ball centred in `X` lies in `X`.
The radius therefore vanishes on the boundary. Its extension by zero is
continuous on the ambient space. A one-dimensional intermediate value argument
then finds a centre on each prescribed backward ray. The zero extension is
used only as a continuous scalar function; no smoothness of it is assumed.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {r s : ℕ}

/-- Full deterministic image makes every centre in the domain admissible. -/
theorem SetValuedSystem.ball_subset_domain_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s)
    (himage : system.map '' system.domain = system.domain) (y : E)
    (hy : y ∈ system.domain) :
    Metric.closedBall y (system.radius y) ⊆ system.domain := by
  have hyimage : y ∈ system.map '' system.domain := by rw [himage]; exact hy
  obtain ⟨x, hx, rfl⟩ := hyimage
  exact system.ball_into_domain x hx

/-- A positive-radius admissible centre is interior, so the radius vanishes
on the boundary when the deterministic image is the whole domain. -/
theorem SetValuedSystem.radius_eq_zero_on_frontier_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s)
    (himage : system.map '' system.domain = system.domain) (y : E)
    (hy : y ∈ frontier system.domain) : system.radius y = 0 := by
  have hyX : y ∈ system.domain := system.regular_closed.isClosed.frontier_subset hy
  apply le_antisymm _ (system.radius_nonneg y hyX)
  apply le_of_not_gt
  intro hpositive
  apply hy.2
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (Metric.ball_mem_nhds y hpositive)
    (fun z hz => system.ball_subset_domain_of_image_eq_domain himage y hyX
      (Metric.ball_subset_closedBall hz))

/-- Continuous zero extension used only in the scalar existence argument. -/
noncomputable def SetValuedSystem.radiusZeroExtension
    (system : SetValuedSystem (E := E) r s) : E → ℝ := by
  classical
  exact system.domain.piecewise system.radius (fun _ => 0)

theorem SetValuedSystem.radiusZeroExtension_of_mem
    (system : SetValuedSystem (E := E) r s) (y : E) (hy : y ∈ system.domain) :
    system.radiusZeroExtension y = system.radius y := by
  classical
  simp [SetValuedSystem.radiusZeroExtension, hy]

theorem SetValuedSystem.radiusZeroExtension_of_not_mem
    (system : SetValuedSystem (E := E) r s) (y : E) (hy : y ∉ system.domain) :
    system.radiusZeroExtension y = 0 := by
  classical
  simp [SetValuedSystem.radiusZeroExtension, hy]

theorem SetValuedSystem.radiusZeroExtension_nonneg
    (system : SetValuedSystem (E := E) r s) (y : E) :
    0 ≤ system.radiusZeroExtension y := by
  by_cases hy : y ∈ system.domain
  · rw [system.radiusZeroExtension_of_mem y hy]
    exact system.radius_nonneg y hy
  · rw [system.radiusZeroExtension_of_not_mem y hy]

theorem SetValuedSystem.radiusZeroExtension_le_bound
    (system : SetValuedSystem (E := E) r s) (y : E) :
    system.radiusZeroExtension y ≤ system.radius_bound := by
  by_cases hy : y ∈ system.domain
  · rw [system.radiusZeroExtension_of_mem y hy]
    exact system.radius_le_bound y hy
  · rw [system.radiusZeroExtension_of_not_mem y hy]
    exact system.radius_bound_pos.le

/-- Boundary vanishing allows continuous gluing to zero outside the closed domain. -/
theorem SetValuedSystem.continuous_radiusZeroExtension_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s)
    (himage : system.map '' system.domain = system.domain) :
    Continuous system.radiusZeroExtension := by
  classical
  apply continuous_piecewise
  · exact system.radius_eq_zero_on_frontier_of_image_eq_domain himage
  · rw [system.regular_closed.isClosed.closure_eq]
    exact system.radius_extension.continuousOn
  · exact continuousOn_const

/-- Every prescribed ray has a centre whose radius is exactly its distance
parameter. This existence result does not need the contraction condition. -/
theorem SetValuedSystem.exists_centre_on_ray_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s)
    (himage : system.map '' system.domain = system.domain)
    (z u : E) (hz : z ∈ system.domain) :
    ∃ y ∈ system.domain, z = y + system.radius y • u := by
  have hcontinuous : Continuous
      (fun q : ℝ => system.radiusZeroExtension (z - q • u)) :=
    (system.continuous_radiusZeroExtension_of_image_eq_domain himage).comp
      (continuous_const.sub (continuous_id.smul continuous_const))
  obtain ⟨q, hq, hroot⟩ := exists_mem_Icc_isFixedPt_of_mapsTo
    hcontinuous.continuousOn system.radius_bound_pos.le
    (fun q _ => ⟨system.radiusZeroExtension_nonneg (z - q • u),
      system.radiusZeroExtension_le_bound (z - q • u)⟩)
  have hy : z - q • u ∈ system.domain := by
    by_contra houtside
    have hqzero : q = 0 := by
      change system.radiusZeroExtension (z - q • u) = q at hroot
      rw [system.radiusZeroExtension_of_not_mem _ houtside] at hroot
      exact hroot.symm
    exact houtside (by simpa [hqzero] using hz)
  refine ⟨z - q • u, hy, ?_⟩
  have hradius : system.radius (z - q • u) = q := by
    change system.radiusZeroExtension (z - q • u) = q at hroot
    rwa [system.radiusZeroExtension_of_mem _ hy] at hroot
  rw [hradius, sub_add_cancel]

variable [CompleteSpace E]

/-- The actual exponential lift covers every point and unit normal in the
state-space bundle when the deterministic map has full image. -/
theorem SetValuedSystem.exponentialLift_covers_domain_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    ∃ q : system.domain × {n : E // ‖n‖ = 1},
      system.exponentialLift hcontraction q = ((p.1 : E), p.2) := by
  obtain ⟨y, hy, hposition⟩ :=
    system.exists_centre_on_ray_of_image_eq_domain himage p.1 p.2 p.1.property
  have hgradient := hcontraction.norm_radiusGradientOnAmbient y hy
  have hnormal : normalUpdate (system.radiusGradientOnAmbient y)
      ((normalSphereEquiv (system.radiusGradientOnAmbient y) hgradient).symm p.2 : E) =
      (p.2 : E) :=
    congrArg Subtype.val
      ((normalSphereEquiv (system.radiusGradientOnAmbient y) hgradient).apply_symm_apply p.2)
  refine ⟨(⟨y, hy⟩,
    (normalSphereEquiv (system.radiusGradientOnAmbient y) hgradient).symm p.2), ?_⟩
  apply Prod.ext
  · change y + system.radius y • normalUpdate (system.radiusGradientOnAmbient y)
      ((normalSphereEquiv (system.radiusGradientOnAmbient y) hgradient).symm p.2 : E) = p.1
    rw [hnormal]
    exact hposition.symm
  · exact Subtype.ext hnormal

theorem SetValuedSystem.linearLift_surjective_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s)
    (himage : system.map '' system.domain = system.domain) :
    Function.Surjective system.linearLift := by
  intro p
  have hp : p ∈ Set.range system.linearLift := by
    rw [system.range_linearLift]
    change (p.1 : E) ∈ system.map '' system.domain
    rw [himage]
    exact p.1.property
  exact hp

/-- The surjectivity assertion of Theorem 3.14 under the original full-image
hypothesis. The radius may vanish and the domain need not be convex. -/
theorem SetValuedSystem.boundaryMap_surjective_of_image_eq_domain
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (himage : system.map '' system.domain = system.domain) :
    Function.Surjective (system.boundaryMap hcontraction) := by
  intro p
  obtain ⟨q, hq⟩ :=
    system.exponentialLift_covers_domain_of_image_eq_domain hcontraction himage p
  obtain ⟨v, hv⟩ := system.linearLift_surjective_of_image_eq_domain himage q
  refine ⟨v, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    change (system.exponentialLift hcontraction (system.linearLift v)).1 = (p.1 : E)
    rw [hv]
    exact congrArg Prod.fst hq
  · change (system.exponentialLift hcontraction (system.linearLift v)).2 = p.2
    rw [hv]
    exact congrArg Prod.snd hq

end BoundedUncertainty
