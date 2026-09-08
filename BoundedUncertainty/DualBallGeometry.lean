import BoundedUncertainty.DualInflation
import BoundedUncertainty.ContactGeometry
import BoundedUncertainty.RayMonotonicity
import Mathlib.Analysis.Convex.Star
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
The actual dual balls from Definition 4.13. Compactness uses the existing
uniform upper radius bound. Boundary regularity is obtained from a local
squared-distance defining function and the canonical radius gradient.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.isClosed_dualBall
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ) (x : E) :
    IsClosed (dualBall system.radius x) := by
  have hcontinuous : Continuous system.radius := continuousOn_univ.mp
    (hwhole ▸ system.radius_extension.continuousOn)
  exact isClosed_le (continuous_const.dist continuous_id) hcontinuous

omit [CompleteSpace E] in
theorem SetValuedSystem.dualBall_subset_closedBall
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ) (x : E) :
    dualBall system.radius x ⊆ Metric.closedBall x system.radius_bound := by
  intro y hy
  exact (dist_comm y x).le.trans (hy.trans (system.radius_le_bound y (hwhole ▸ mem_univ y)))

omit [CompleteSpace E] in
theorem SetValuedSystem.isCompact_dualBall
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ) (x : E) :
    IsCompact (dualBall system.radius x) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  exact (isCompact_closedBall x system.radius_bound).of_isClosed_subset
    (system.isClosed_dualBall hwhole x) (system.dualBall_subset_closedBall hwhole x)

omit [CompleteSpace E] in
theorem SetValuedSystem.mem_interior_dualBall_of_dist_lt
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (x y : E) (hstrict : dist x y < system.radius y) :
    y ∈ interior (dualBall system.radius x) := by
  have hcontinuous : Continuous system.radius := continuousOn_univ.mp
    (hwhole ▸ system.radius_extension.continuousOn)
  exact mem_interior.mpr ⟨{w | dist x w < system.radius w},
    fun w (hw : dist x w < system.radius w) => hw.le,
    isOpen_lt (continuous_const.dist continuous_id) hcontinuous, hstrict⟩

omit [CompleteSpace E] in
theorem SetValuedSystem.dist_eq_radius_of_mem_frontier_dualBall
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (x y : E) (hy : y ∈ frontier (dualBall system.radius x)) :
    dist x y = system.radius y := by
  have hle : dist x y ≤ system.radius y :=
    (system.isClosed_dualBall hwhole x).frontier_subset hy
  apply le_antisymm hle
  exact le_of_not_gt (fun hlt => hy.2 (system.mem_interior_dualBall_of_dist_lt hwhole x y hlt))

theorem SetValuedSystem.contactGradient_ne_zero_of_dual_contact
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (x y : E) (hy : y ∈ system.domain) (hpositive : 0 < system.radius y)
    (hcontact : dist x y = system.radius y) : system.contactGradient x y ≠ 0 := by
  intro hzero
  have hscaled := congrArg (fun v : E => (2 : ℝ)⁻¹ • v) hzero
  have hposition : y - x - system.radius y • system.radiusGradientOnAmbient y = 0 := by
    convert hscaled using 1 <;> simp only [SetValuedSystem.contactGradient] <;> module
  have hnorm := congrArg norm (sub_eq_zero.mp hposition)
  rw [norm_smul, Real.norm_of_nonneg hpositive.le] at hnorm
  have hdist : ‖y - x‖ = system.radius y := by
    simpa only [dist_eq_norm, norm_sub_rev] using hcontact
  rw [hdist] at hnorm
  have hbound := hcontraction.norm_radiusGradientOnAmbient y hy
  nlinarith

/-- Positive radius and contraction produce genuine local C1 boundary data. -/
theorem SetValuedSystem.exists_C1BoundaryAt_dualBall
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (x y : E)
    (hy : y ∈ frontier (dualBall system.radius x)) (hpositive : 0 < system.radius y) :
    Nonempty (C1BoundaryAt (dualBall system.radius x) y) := by
  have hyX : y ∈ system.domain := hwhole ▸ mem_univ y
  obtain ⟨extension⟩ := system.radius_extension y hyX
  have hsmooth : ContDiffOn ℝ 1 extension.extension extension.neighborhood :=
    extension.contDiffOn_extension.of_le (by exact_mod_cast system.radius_order_pos)
  have hcontact := system.dist_eq_radius_of_mem_frontier_dualBall hwhole x y hy
  refine ⟨C1BoundaryAt.ofDefiningFunction (dualBall system.radius x) y
    extension.neighborhood extension.isOpen_neighborhood extension.mem_neighborhood
    (fun w : E => ‖w - x‖ ^ 2 - (extension.extension w) ^ 2)
    (((contDiff_id.sub contDiff_const).norm_sq ℝ).contDiffOn.sub (hsmooth.pow 2))
    ?_ ?_ (system.contactGradient x y)
    (system.hasGradientAt_contactPotential_extension y x hyX extension)
    (system.contactGradient_ne_zero_of_dual_contact hcontraction x y hyX hpositive hcontact)⟩
  · change ‖y - x‖ ^ 2 - (extension.extension y) ^ 2 = 0
    rw [extension.agrees ⟨hyX, extension.mem_neighborhood⟩]
    have hnorm : ‖y - x‖ = system.radius y := by
      simpa only [dist_eq_norm, norm_sub_rev] using hcontact
    rw [hnorm, sub_self]
  · intro w hw
    change dist x w ≤ system.radius w ↔ ‖w - x‖ ^ 2 - (extension.extension w) ^ 2 ≤ 0
    rw [extension.agrees ⟨hwhole ▸ mem_univ w, hw⟩]
    rw [dist_comm x w]
    exact mem_closedBall_iff_sqDist_sub_sqRadius_nonpos x w (system.radius w)
      (system.radius_nonneg w (hwhole ▸ mem_univ w))

/-- Pointwise contraction gives a strict secant bound on a whole-space system. -/
theorem SetValuedSystem.radius_sub_radius_lt_dist
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (y w : E) (hne : y ≠ w) :
    system.radius y - system.radius w < dist y w := by
  have hnonzero : w - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hnorm : 0 < ‖w - y‖ := norm_pos_iff.mpr hnonzero
  have hendpoint : w - ‖w - y‖ • (‖w - y‖⁻¹ • (w - y)) = y := by
    rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    abel
  have hmono := system.strictMonoOn_radius_ray hcontraction w
    (‖w - y‖⁻¹ • (w - y)) (norm_smul_inv_norm hnonzero) 0 ‖w - y‖
    (fun q _ => hwhole ▸ mem_univ (w - q • (‖w - y‖⁻¹ • (w - y))))
  have hstrict := hmono ⟨le_rfl, hnorm.le⟩ ⟨hnorm.le, le_rfl⟩ hnorm
  simp only [zero_smul, sub_zero, zero_sub, hendpoint] at hstrict
  rw [dist_eq_norm, norm_sub_rev]
  linarith

theorem SetValuedSystem.radius_sub_radius_le_dist
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (y w : E) :
    system.radius y - system.radius w ≤ dist y w := by
  by_cases heq : y = w
  · simp [heq]
  · exact (system.radius_sub_radius_lt_dist hwhole hcontraction y w heq).le

/-- All segments from the distinguished point stay in its actual dual ball. -/
theorem SetValuedSystem.starConvex_dualBall
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (x : E) :
    StarConvex ℝ x (dualBall system.radius x) := by
  intro y hy a b ha hb hab
  have hfirst : dist x (a • x + b • y) = b * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : x - (a • x + b • y) = b • (x - y) := by
      have : a = 1 - b := by linarith
      rw [this]
      module
    rw [heq, norm_smul, Real.norm_of_nonneg hb]
  have hsecond : dist y (a • x + b • y) = a * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : y - (a • x + b • y) = a • (y - x) := by
      have : b = 1 - a := by linarith
      rw [this]
      module
    rw [heq, norm_smul, Real.norm_of_nonneg ha, norm_sub_rev]
  have hbound := system.radius_sub_radius_le_dist hwhole hcontraction y (a • x + b • y)
  change dist x (a • x + b • y) ≤ system.radius (a • x + b • y)
  change dist x y ≤ system.radius y at hy
  rw [hfirst]
  rw [hsecond] at hbound
  have hsum : a * dist x y + b * dist x y = dist x y := by
    rw [← add_mul, hab, one_mul]
  linarith

theorem C1BoundaryAt.mem_interior_of_defining_neg {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) (w : E) (hw : w ∈ boundary.neighborhood)
    (hnegative : boundary.defining w < 0) : w ∈ interior B := by
  have hcontinuous := boundary.contDiffOn_defining.continuousOn.continuousAt
    (boundary.isOpen_neighborhood.mem_nhds hw)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (inter_mem
    (boundary.isOpen_neighborhood.mem_nhds hw)
    (hcontinuous.preimage_mem_nhds (Iio_mem_nhds hnegative)))
  intro z hz
  exact (boundary.mem_iff z hz.1).mpr hz.2.le

/-- A regular defining gradient gives actual interior points approaching the boundary. -/
theorem C1BoundaryAt.mem_closure_interior {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) : y ∈ closure (interior B) := by
  have hnegative := eventually_neg_right_of_hasDerivAt
    (boundary.hasDerivAt_defining_ray (-boundary.normal))
    (by simpa using boundary.defining_eq_zero) (by
      simp only [inner_neg_right, real_inner_self_eq_norm_sq, boundary.normal_unit, one_pow]
      norm_num)
  have hcontinuous : Continuous (fun t : ℝ => y + t • (-boundary.normal)) := by fun_prop
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), y + t • (-boundary.normal) ∈ boundary.neighborhood :=
    hcontinuous.continuousAt.preimage_mem_nhds (by
      simpa using boundary.isOpen_neighborhood.mem_nhds boundary.mem_neighborhood)
  have hinterior : ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • (-boundary.normal) ∈ interior B := by
    filter_upwards [hnegative, hnear.filter_mono nhdsWithin_le_nhds] with t ht htU
    exact boundary.mem_interior_of_defining_neg _ htU ht
  apply mem_closure_of_tendsto (f := fun t : ℝ => y + t • (-boundary.normal))
    (b := 𝓝[>] (0 : ℝ)) ?_ hinterior
  simpa using (hcontinuous.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds

theorem SetValuedSystem.isRegularClosed_dualBall
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (x : E)
    (hpositive : ∀ y ∈ frontier (dualBall system.radius x), 0 < system.radius y) :
    IsRegularClosed (dualBall system.radius x) := by
  apply Subset.antisymm
    (closure_minimal interior_subset (system.isClosed_dualBall hwhole x))
  intro y hy
  by_cases hinterior : y ∈ interior (dualBall system.radius x)
  · exact subset_closure hinterior
  · have hfrontier : y ∈ frontier (dualBall system.radius x) := ⟨subset_closure hy, hinterior⟩
    obtain ⟨boundary⟩ := system.exists_C1BoundaryAt_dualBall hwhole hcontraction x y
      hfrontier (hpositive y hfrontier)
    exact boundary.mem_closure_interior

end BoundedUncertainty
