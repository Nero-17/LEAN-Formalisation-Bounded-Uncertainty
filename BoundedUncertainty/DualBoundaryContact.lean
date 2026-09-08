import BoundedUncertainty.DualInflationGeometry
import BoundedUncertainty.ContributorFormula

/-!
Normals at an attained nearest-point contact for the dual construction.
The source normal is obtained from an actual exterior-ball defining function.
The target normal is compared with its actual constituent dual ball.
No differentiability of the distance to a set is assumed or asserted.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Actual C1 boundary data for the closed exterior of a positive-radius ball. -/
noncomputable def C1BoundaryAt.closedBallExterior (y : E) (R : ℝ) (x : E)
    (hR : 0 < R) (hcontact : dist x y = R) :
    C1BoundaryAt {w : E | R ≤ dist w y} x := by
  have hnorm : ‖x - y‖ = R := by simpa only [dist_eq_norm] using hcontact
  have hnonzero : x - y ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    exact hR.ne' hnorm.symm
  refine C1BoundaryAt.ofDefiningFunction {w : E | R ≤ dist w y} x
    univ isOpen_univ (mem_univ x) (fun w : E => -(‖w - y‖ ^ 2 - R ^ 2))
    ((((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const).neg.contDiffOn)
    ?_ ?_ (-((2 : ℝ) • (x - y))) ?_ (neg_ne_zero.mpr (smul_ne_zero (by norm_num) hnonzero))
  · change -(‖x - y‖ ^ 2 - R ^ 2) = 0
    rw [hnorm, sub_self, neg_zero]
  · intro w _
    change R ≤ dist w y ↔ -(‖w - y‖ ^ 2 - R ^ 2) ≤ 0
    rw [dist_eq_norm]
    constructor <;> intro h <;> nlinarith [norm_nonneg (w - y)]
  · rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (hasGradientAt_sqDist_sub_sqRadius y x R).hasFDerivAt.neg

theorem C1BoundaryAt.closedBallExterior_normal (y : E) (R : ℝ) (x : E)
    (hR : 0 < R) (hcontact : dist x y = R) :
    (C1BoundaryAt.closedBallExterior y R x hR hcontact).normal = R⁻¹ • (y - x) := by
  change ‖-((2 : ℝ) • (x - y))‖⁻¹ • (-((2 : ℝ) • (x - y))) = _
  have hnorm : ‖x - y‖ = R := by simpa only [dist_eq_norm] using hcontact
  rw [norm_neg, norm_smul, Real.norm_ofNat, hnorm, mul_inv_rev, smul_neg, smul_smul,
    mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), mul_one]
  module

theorem mem_frontier_of_nearest_contact (A : Set E) (x y : E) (R : ℝ)
    (hx : x ∈ A) (hR : 0 < R) (hcontact : dist x y = R)
    (hnearest : ∀ w ∈ A, R ≤ dist w y) : x ∈ frontier A := by
  refine ⟨subset_closure hx, ?_⟩
  intro hinterior
  exact (C1BoundaryAt.closedBallExterior y R x hR hcontact).mem_frontier.2
    (interior_mono hnearest hinterior)

theorem C1BoundaryAt.normal_eq_radial_of_nearest_contact (A : Set E) (x y : E) (R : ℝ)
    (source : C1BoundaryAt A x) (hR : 0 < R) (hcontact : dist x y = R)
    (hnearest : ∀ w ∈ A, R ≤ dist w y) : source.normal = R⁻¹ • (y - x) :=
  (source.normal_eq_of_subset (C1BoundaryAt.closedBallExterior y R x hR hcontact)
    hnearest).trans (C1BoundaryAt.closedBallExterior_normal y R x hR hcontact)

variable {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.mem_interior_dualInflation_of_infDist_lt
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (A : Set E) (hne : A.Nonempty) (y : E) (hstrict : Metric.infDist y A < system.radius y) :
    y ∈ interior (dualInflation system.radius A) := by
  have hcontinuous : Continuous system.radius := continuousOn_univ.mp
    (hwhole ▸ system.radius_extension.continuousOn)
  exact mem_interior.mpr ⟨{w | Metric.infDist w A < system.radius w},
    infDist_strict_sublevel_subset_dualInflation system.radius A hne,
    isOpen_lt (Metric.continuous_infDist_pt A) hcontinuous, hstrict⟩

omit [CompleteSpace E] in
/-- The level equation follows from the actual union frontier, even before distance attainment. -/
theorem SetValuedSystem.infDist_eq_radius_of_mem_frontier_dualInflation
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (A : Set E) (hne : A.Nonempty) (y : E)
    (hy : y ∈ frontier (dualInflation system.radius A)) :
    Metric.infDist y A = system.radius y := by
  have hcontinuous : Continuous system.radius := continuousOn_univ.mp
    (hwhole ▸ system.radius_extension.continuousOn)
  have hclosed : IsClosed {w | Metric.infDist w A ≤ system.radius w} :=
    isClosed_le (Metric.continuous_infDist_pt A) hcontinuous
  have hle : Metric.infDist y A ≤ system.radius y :=
    closure_minimal (dualInflation_subset_infDist_sublevel system.radius A) hclosed hy.1
  apply le_antisymm hle
  exact le_of_not_gt (fun hlt => hy.2
    (system.mem_interior_dualInflation_of_infDist_lt hwhole A hne y hlt))

/-- The actual dual-ball contact gradient has the target's outward orientation. -/
theorem SetValuedSystem.exists_nonneg_dual_contact_multiplier
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (A : Set E) (x y : E) (hx : x ∈ A)
    (target : C1BoundaryAt (dualInflation system.radius A) y)
    (hpositive : 0 < system.radius y) (hcontact : dist x y = system.radius y) :
    ∃ coefficient : ℝ, 0 ≤ coefficient ∧
      system.contactGradient x y = coefficient • target.normal := by
  have hsubset : dualBall system.radius x ⊆ dualInflation system.radius A := by
    intro w hw
    exact (mem_dualInflation system.radius A w).mpr ⟨x, hx, hw⟩
  have hfrontier : y ∈ frontier (dualBall system.radius x) := by
    refine ⟨subset_closure hcontact.le, ?_⟩
    exact fun hyint => target.mem_frontier.2 (interior_mono hsubset hyint)
  obtain ⟨boundary⟩ := system.exists_C1BoundaryAt_dualBall hwhole hcontraction x y
    hfrontier hpositive
  have hnormal := boundary.normal_eq_of_subset target hsubset
  have hyX : y ∈ system.domain := hwhole ▸ mem_univ y
  obtain ⟨extension⟩ := system.radius_extension y hyX
  have hmax : IsLocalMaxOn
      (fun w : E => ‖w - x‖ ^ 2 - (extension.extension w) ^ 2) (dualBall system.radius x) y := by
    show ∀ᶠ w in 𝓝[dualBall system.radius x] y,
      ‖w - x‖ ^ 2 - (extension.extension w) ^ 2 ≤
        ‖y - x‖ ^ 2 - (extension.extension y) ^ 2
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)] with w hw hwU
    rw [extension.agrees ⟨hwhole ▸ mem_univ w, hwU⟩,
      extension.agrees ⟨hyX, extension.mem_neighborhood⟩]
    have hnorm : ‖y - x‖ = system.radius y := by
      simpa only [dist_eq_norm, norm_sub_rev] using hcontact
    rw [hnorm, sub_self]
    apply (mem_closedBall_iff_sqDist_sub_sqRadius_nonpos x w (system.radius w)
      (system.radius_nonneg w (hwhole ▸ mem_univ w))).mp
    exact (dist_comm w x).trans_le hw
  obtain ⟨coefficient, hnonneg, heq⟩ := boundary.exists_nonneg_smul_of_isLocalMaxOn _ _
    (system.hasGradientAt_contactPotential_extension y x hyX extension) hmax
  exact ⟨coefficient, hnonneg, hnormal ▸ heq⟩

/-- The exact exponential formula at an attained dual-boundary contact. -/
theorem SetValuedSystem.exponentialMap_inward_of_dual_contact
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) (A : Set E) (x y : E)
    (source : C1BoundaryAt A x) (target : C1BoundaryAt (dualInflation system.radius A) y)
    (hpositive : 0 < system.radius y) (hcontact : dist x y = system.radius y)
    (hnearest : ∀ w ∈ A, system.radius y ≤ dist w y) :
    exponentialMap system.radius system.radiusGradientOnAmbient (y, -target.normal) =
      (x, -source.normal) := by
  have hsource := source.normal_eq_radial_of_nearest_contact A x y (system.radius y)
    hpositive hcontact hnearest
  have hposition : system.radius y • source.normal = y - x := by
    rw [hsource, smul_smul, mul_inv_cancel₀ hpositive.ne', one_smul]
  obtain ⟨coefficient, hnonneg, heq⟩ := system.exists_nonneg_dual_contact_multiplier hwhole
    hcontraction A x y source.mem target hpositive hcontact
  have hscaled : system.radius y • (-source.normal) +
      system.radius y • system.radiusGradientOnAmbient y =
        (coefficient / 2) • (-target.normal) := by
    have hscale := congrArg (fun v : E => (-(2 : ℝ)⁻¹) • v) heq
    change (-(2 : ℝ)⁻¹) • ((2 : ℝ) • (y - x) -
      (2 * system.radius y) • system.radiusGradientOnAmbient y) = _ at hscale
    rw [← hposition] at hscale
    convert hscale using 1 <;> module
  have hnormal := normalUpdate_eq_of_nonneg_scaled_contact
    (system.radiusGradientOnAmbient y) (-target.normal) (-source.normal)
    (hcontraction.norm_radiusGradientOnAmbient y (hwhole ▸ mem_univ y))
    ((norm_neg _).trans target.normal_unit) ((norm_neg _).trans source.normal_unit)
    (system.radius y) (coefficient / 2) hpositive (div_nonneg hnonneg (by norm_num)) hscaled
  apply Prod.ext
  · change y + system.radius y • normalUpdate (system.radiusGradientOnAmbient y)
      (-target.normal) = x
    rw [hnormal, smul_neg, hposition]
    abel
  · exact hnormal

end BoundedUncertainty
