import BoundedUncertainty.RayMonotonicity
import BoundedUncertainty.InflationGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Lemma 3.4: a centre contributing to the boundary of an inflation is itself
on the boundary of the centre set. The pointwise assertion does not require
compactness or a smooth boundary. Compactness is used separately for existence.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem radius_le_dist_of_mem_frontier_inflation (radius : E → ℝ) (B : Set E)
    (z : E) (hz : z ∈ frontier (inflation radius B)) (y : E) (hy : y ∈ B) :
    radius y ≤ dist z y := by
  apply le_of_not_gt
  intro hlt
  have hsubset : Metric.ball y (radius y) ⊆ inflation radius B := by
    intro w hw
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, Metric.ball_subset_closedBall hw⟩⟩
  exact hz.2 ((Metric.isOpen_ball.subset_interior_iff.mpr hsubset) hlt)

theorem subset_inflation_of_nonneg (radius : E → ℝ) (B : Set E)
    (hradius : ∀ y ∈ B, 0 ≤ radius y) : B ⊆ inflation radius B := by
  intro y hy
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, Metric.mem_closedBall_self (hradius y hy)⟩⟩

variable [InnerProductSpace ℝ E] [CompleteSpace E] {r s : ℕ}

/-- An interior contributor would give a local minimum of a scalar function
whose derivative is strictly positive. -/
theorem SetValuedSystem.not_mem_interior_of_contributing_direction
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z u : E)
    (hz : z ∈ frontier (inflation system.radius B)) (hu : ‖u‖ = 1)
    (hradius : 0 < system.radius y) (hroot : z - system.radius y • u = y) :
    y ∉ interior B := by
  intro hy
  have hcontinuous : Continuous (fun q : ℝ => z - q • u) := by fun_prop
  have hnear : ∀ᶠ q in 𝓝 (system.radius y), z - q • u ∈ B :=
    hcontinuous.continuousAt.preimage_mem_nhds (by
      rw [hroot]
      exact mem_interior_iff_mem_nhds.mp hy)
  have hmin : IsLocalMin (fun q : ℝ => q - system.radius (z - q • u))
      (system.radius y) := by
    show ∀ᶠ q in 𝓝 (system.radius y),
      system.radius y - system.radius (z - system.radius y • u) ≤
        q - system.radius (z - q • u)
    filter_upwards [hnear, Ioi_mem_nhds hradius] with q hq hqpos
    rw [hroot, sub_self]
    have hbound := radius_le_dist_of_mem_frontier_inflation system.radius B z hz
      (z - q • u) hq
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
      abs_of_pos hqpos, hu, mul_one] at hbound
    linarith
  have hderiv := (hasDerivAt_id (system.radius y)).sub
    (system.hasDerivAt_radius_ray z u (system.radius y) (hnear.mono fun _ hq => hB hq))
  have hzero := hmin.hasDerivAt_eq_zero hderiv
  rw [hroot] at hzero
  have hbound := neg_le_of_abs_le (abs_real_inner_le_norm
    (system.radiusGradientOnAmbient y) u)
  rw [hu, mul_one] at hbound
  have hlt := hcontraction.norm_radiusGradientOnAmbient y (hB (interior_subset hy))
  linarith

/-- Lemma 3.4, including zero-radius contributors and arbitrary centre-set boundaries. -/
theorem SetValuedSystem.contributor_mem_frontier
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z : E)
    (hy : y ∈ B) (hz : z ∈ frontier (inflation system.radius B))
    (hcontact : dist z y = system.radius y) : y ∈ frontier B := by
  refine ⟨subset_closure hy, ?_⟩
  intro hyint
  have hradius : 0 < system.radius y := by
    apply lt_of_le_of_ne (system.radius_nonneg y (hB hy))
    intro hzero
    have hzy : z = y := dist_eq_zero.mp (hcontact.trans hzero.symm)
    subst z
    exact hz.2 (interior_mono
      (subset_inflation_of_nonneg system.radius B (fun w hw => system.radius_nonneg w (hB hw)))
      hyint)
  have hnonzero : z - y ≠ 0 := by
    intro hzero
    have hnorm : ‖z - y‖ = system.radius y := by simpa only [dist_eq_norm] using hcontact
    rw [hzero, norm_zero] at hnorm
    linarith
  apply system.not_mem_interior_of_contributing_direction hcontraction B hB y z
    (‖z - y‖⁻¹ • (z - y)) hz (norm_smul_inv_norm hnonzero) hradius _ hyint
  rw [← hcontact, dist_eq_norm, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnonzero),
    one_smul, sub_sub_cancel]

/-- The set inclusion in Lemma 3.4, with contribution existence proved from compactness. -/
theorem SetValuedSystem.frontier_inflation_subset
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (hcompact : IsCompact B) :
    frontier (inflation system.radius B) ⊆ inflation system.radius (frontier B) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  apply frontier_inflation_subset_of_contributors_on_frontier system.radius B hcompact
    (system.radius_extension.continuousOn.mono hB)
    (fun y hy => system.radius_nonneg y (hB hy))
  intro z hz y hy hcontact
  exact system.contributor_mem_frontier hcontraction B hB y z hy hz hcontact

/-- The same boundary inclusion for the actual one-step set-valued image. -/
theorem SetValuedSystem.frontier_setValuedImage_subset_inflation_frontier_image
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A) :
    frontier (setValuedImage system.map system.radius A) ⊆
      inflation system.radius (frontier (system.map '' A)) := by
  rw [setValuedImage_eq_inflation]
  apply system.frontier_inflation_subset hcontraction
  · rintro y ⟨x, hx, rfl⟩
    exact system.map_into_domain (hA hx)
  · exact hcompact.image_of_continuousOn
      (system.diffeomorphism.forward_extension.continuousOn.mono hA)

end BoundedUncertainty
