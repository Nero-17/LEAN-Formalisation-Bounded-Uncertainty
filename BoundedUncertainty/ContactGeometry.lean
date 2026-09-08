import BoundedUncertainty.BoundaryContributors
import BoundedUncertainty.SphereBoundary
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.Module

/-!
The contact normal and the signed multiplier in Lemmas 3.6 and 3.7.
The variational proof uses the squared-distance potential, which is smooth
even when the contact radius is zero. All radius derivatives come from the
given local extensions and agree with the canonical radius gradient.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Lemma 3.6: a positive-radius ball tangent from inside identifies the recipient normal. -/
theorem C1BoundaryAt.normal_eq_radial_of_ball_subset {C : Set E} {z : E}
    (boundary : C1BoundaryAt C z) (y : E) (R : ℝ) (hR : 0 < R)
    (hz : z ∈ Metric.sphere y R) (hball : Metric.closedBall y R ⊆ C) :
    boundary.normal = ‖z - y‖⁻¹ • (z - y) := by
  rw [← C1BoundaryAt.closedBall_normal y R z hR hz]
  exact ((C1BoundaryAt.closedBall y R z hR hz).normal_eq_of_subset boundary hball).symm

theorem C1BoundaryAt.normal_eq_radial_of_inflation_contact (radius : E → ℝ) (B : Set E)
    (y z : E) (boundary : C1BoundaryAt (inflation radius B) z)
    (hy : y ∈ B) (hR : 0 < radius y) (hz : dist z y = radius y) :
    boundary.normal = ‖z - y‖⁻¹ • (z - y) :=
  boundary.normal_eq_radial_of_ball_subset y (radius y) hR hz
    (closedBall_subset_inflation radius B y hy)

theorem hasGradientAt_sqDist_sub_sq (radius : E → ℝ) (y z gradient : E)
    (hgradient : HasGradientAt radius gradient y) :
    HasGradientAt (fun w : E => ‖w - z‖ ^ 2 - (radius w) ^ 2)
      ((2 : ℝ) • (y - z) - (2 * radius y) • gradient) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((hasFDerivAt_id y).sub_const z).norm_sq.sub
    (hgradient.hasFDerivAt.pow 2)) using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

variable {r s : ℕ}

/-- The canonical centre-gradient of the squared-distance contact potential. -/
noncomputable def SetValuedSystem.contactGradient
    (system : SetValuedSystem (E := E) r s) (z y : E) : E :=
  (2 : ℝ) • (y - z) - (2 * system.radius y) • system.radiusGradientOnAmbient y

/-- Each admissible radius extension produces the same actual contact gradient. -/
theorem SetValuedSystem.hasGradientAt_contactPotential_extension
    (system : SetValuedSystem (E := E) r s) (y z : E) (hy : y ∈ system.domain)
    (extension : LocalExtensionAt r system.domain system.radius y) :
    HasGradientAt (fun w : E => ‖w - z‖ ^ 2 - (extension.extension w) ^ 2)
      (system.contactGradient z y) y := by
  have hsmooth : ContDiffOn ℝ 1 extension.extension extension.neighborhood :=
    extension.contDiffOn_extension.of_le (by exact_mod_cast system.radius_order_pos)
  have hdiff := hsmooth.differentiableOn_one.differentiableAt
    (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  have hgradient : HasGradientAt extension.extension (system.radiusGradientOnAmbient y) y := by
    rw [(system.radiusGradientOnAmbient_apply ⟨y, hy⟩).trans
      (system.radiusGradient_eq_extension system.radius_order_pos extension
        ⟨y, hy⟩ extension.mem_neighborhood)]
    exact hdiff.hasGradientAt
  have hresult := hasGradientAt_sqDist_sub_sq extension.extension y z
    (system.radiusGradientOnAmbient y) hgradient
  simpa only [extension.agrees ⟨hy, extension.mem_neighborhood⟩,
    SetValuedSystem.contactGradient] using hresult

omit [CompleteSpace E] in
/-- The negative contact potential has a local maximum over the centre set. -/
theorem SetValuedSystem.isLocalMaxOn_neg_contactPotential_extension
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (y z : E) (hy : y ∈ B) (hz : z ∈ frontier (inflation system.radius B))
    (hcontact : dist z y = system.radius y)
    (extension : LocalExtensionAt r system.domain system.radius y) :
    IsLocalMaxOn (fun w : E => -(‖w - z‖ ^ 2 - (extension.extension w) ^ 2)) B y := by
  have hnorm : ‖y - z‖ = system.radius y := by
    simpa only [dist_eq_norm, norm_sub_rev] using hcontact
  show ∀ᶠ w in 𝓝[B] y,
    -(‖w - z‖ ^ 2 - (extension.extension w) ^ 2) ≤
      -(‖y - z‖ ^ 2 - (extension.extension y) ^ 2)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)] with w hw hwU
  rw [extension.agrees ⟨hB hw, hwU⟩,
    extension.agrees ⟨hB hy, extension.mem_neighborhood⟩, hnorm, sub_self, neg_zero]
  have hbound := radius_le_dist_of_mem_frontier_inflation system.radius B z hz w hw
  rw [dist_eq_norm, norm_sub_rev] at hbound
  nlinarith [system.radius_nonneg w (hB hw), norm_nonneg (w - z)]

/-- Lemma 3.7 with a proved sign, including the zero-radius case. -/
theorem SetValuedSystem.exists_nonneg_contact_multiplier
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (y z : E) (boundary : C1BoundaryAt B y)
    (hz : z ∈ frontier (inflation system.radius B))
    (hcontact : dist z y = system.radius y) :
    ∃ coefficient : ℝ, 0 ≤ coefficient ∧
      system.contactGradient z y = (-2 * coefficient) • boundary.normal := by
  obtain ⟨extension⟩ := system.radius_extension y (hB boundary.mem)
  have hgradient : HasGradientAt
      (fun w : E => -(‖w - z‖ ^ 2 - (extension.extension w) ^ 2))
      (-system.contactGradient z y) y := by
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (system.hasGradientAt_contactPotential_extension y z (hB boundary.mem)
      extension).hasFDerivAt.neg
  obtain ⟨coefficient, hnonneg, heq⟩ := boundary.exists_nonneg_smul_of_isLocalMaxOn
    _ _ hgradient (system.isLocalMaxOn_neg_contactPotential_extension B hB y z
      boundary.mem hz hcontact extension)
  refine ⟨coefficient / 2, div_nonneg hnonneg (by norm_num), ?_⟩
  have hnegative := congrArg Neg.neg heq
  rw [neg_neg, ← neg_smul] at hnegative
  have hscalar : (-2 : ℝ) * (coefficient / 2) = -coefficient := by ring
  rw [hscalar]
  exact hnegative

/-- The multiplier gives the centre-to-recipient vector relation used in Theorem 3.8. -/
theorem SetValuedSystem.exists_nonneg_contact_position_multiplier
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (y z : E) (boundary : C1BoundaryAt B y)
    (hz : z ∈ frontier (inflation system.radius B))
    (hcontact : dist z y = system.radius y) :
    ∃ coefficient : ℝ, 0 ≤ coefficient ∧
      z - y + system.radius y • system.radiusGradientOnAmbient y =
        coefficient • boundary.normal := by
  obtain ⟨coefficient, hnonneg, heq⟩ :=
    system.exists_nonneg_contact_multiplier B hB y z boundary hz hcontact
  refine ⟨coefficient, hnonneg, ?_⟩
  have hscaled := congrArg (fun v : E => (- (2 : ℝ)⁻¹) • v) heq
  change (- (2 : ℝ)⁻¹) •
    ((2 : ℝ) • (y - z) - (2 * system.radius y) • system.radiusGradientOnAmbient y) =
      (- (2 : ℝ)⁻¹) • ((-2 * coefficient) • boundary.normal) at hscaled
  convert hscaled using 1 <;> module

end BoundedUncertainty
