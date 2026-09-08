import BoundedUncertainty.ContactGeometry
import Mathlib.Tactic.Module

/-!
# The actual contributor-to-recipient formula

This proves Theorem 3.8 from genuine boundary contacts, with explicit local C1
boundary data. The zero-radius branch uses the minimum of the radius over the
centre set; it does not assume that the ambient gradient vanishes there.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A gradient parallel to a unit normal leaves that normal fixed, regardless of its sign. -/
theorem normalUpdate_smul_self (a : ℝ) (n : E) (hn : ‖n‖ = 1) :
    normalUpdate (a • n) n = n := by
  simp [normalUpdate, real_inner_smul_right, hn,
    norm_smul, Real.norm_eq_abs, sq_abs, add_smul]

/-- A nonnegative contact multiple is positive under contraction and determines the normal update. -/
theorem normalUpdate_eq_of_nonneg_multiple (gradient n u : E)
    (hgradient : ‖gradient‖ < 1) (hn : ‖n‖ = 1) (hu : ‖u‖ = 1)
    (coefficient : ℝ) (hcoefficient : 0 ≤ coefficient)
    (heq : u + gradient = coefficient • n) : normalUpdate gradient n = u := by
  have hpositive : 0 < coefficient := by
    apply lt_of_le_of_ne hcoefficient
    intro hzero
    exact unit_add_gradient_ne_zero gradient u hgradient hu
      (by simpa only [← hzero, zero_smul] using heq)
  have hnormalize : ‖u + gradient‖⁻¹ • (u + gradient) = n := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hpositive, hn, mul_one,
      smul_smul, inv_mul_cancel₀ (ne_of_gt hpositive), one_smul]
  simpa only [hnormalize] using normalUpdate_normalize_add_gradient gradient u hgradient hu

theorem normalUpdate_eq_of_nonneg_scaled_contact (gradient n u : E)
    (hgradient : ‖gradient‖ < 1) (hn : ‖n‖ = 1) (hu : ‖u‖ = 1)
    (radius coefficient : ℝ) (hradius : 0 < radius) (hcoefficient : 0 ≤ coefficient)
    (heq : radius • u + radius • gradient = coefficient • n) :
    normalUpdate gradient n = u := by
  apply normalUpdate_eq_of_nonneg_multiple gradient n u hgradient hn hu
    (radius⁻¹ * coefficient) (mul_nonneg (inv_nonneg.mpr hradius.le) hcoefficient)
  have hscaled := congrArg (fun v : E => radius⁻¹ • v) heq
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hradius), one_smul] using hscaled

variable [CompleteSpace E]

/-- The geometric position formula includes zero-radius contacts. -/
theorem C1BoundaryAt.position_eq_of_inflation_contact (radius : E → ℝ) (B : Set E)
    (y z : E) (recipient : C1BoundaryAt (inflation radius B) z)
    (hy : y ∈ B) (hnonneg : 0 ≤ radius y) (hcontact : dist z y = radius y) :
    z = y + radius y • recipient.normal := by
  by_cases hzero : radius y = 0
  · have hzy : z = y := dist_eq_zero.mp (hcontact.trans hzero)
    simpa only [hzero, zero_smul, add_zero] using hzy
  · have hpositive : 0 < radius y := lt_of_le_of_ne hnonneg (Ne.symm hzero)
    have hradial := recipient.normal_eq_radial_of_inflation_contact radius B y z hy hpositive hcontact
    have hnorm : ‖z - y‖ = radius y := by simpa only [dist_eq_norm] using hcontact
    rw [hradial, smul_smul, hnorm, mul_inv_cancel₀ hzero, one_smul]
    abel

variable {r s : ℕ}

/-- A zero of the nonnegative radius on the centre set has an inward normal gradient.
Only a local radius extension is differentiated. -/
theorem SetValuedSystem.exists_nonpos_radiusGradient_smul_at_zero
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (y : E) (boundary : C1BoundaryAt B y) (hzero : system.radius y = 0) :
    ∃ coefficient : ℝ, 0 ≤ coefficient ∧
      system.radiusGradientOnAmbient y = (-coefficient) • boundary.normal := by
  obtain ⟨extension⟩ := system.radius_extension y (hB boundary.mem)
  have hsmooth : ContDiffOn ℝ 1 extension.extension extension.neighborhood :=
    extension.contDiffOn_extension.of_le (by exact_mod_cast system.radius_order_pos)
  have hgradient : HasGradientAt extension.extension (system.radiusGradientOnAmbient y) y := by
    rw [(system.radiusGradientOnAmbient_apply ⟨y, hB boundary.mem⟩).trans
      (system.radiusGradient_eq_extension system.radius_order_pos extension
        ⟨y, hB boundary.mem⟩ extension.mem_neighborhood)]
    exact (hsmooth.differentiableOn_one.differentiableAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)).hasGradientAt
  have hnegativeGradient : HasGradientAt (fun w => -extension.extension w)
      (-system.radiusGradientOnAmbient y) y := by
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact hgradient.hasFDerivAt.neg
  have hmax : IsLocalMaxOn (fun w => -extension.extension w) B y := by
    show ∀ᶠ w in 𝓝[B] y, -extension.extension w ≤ -extension.extension y
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)] with w hw hwU
    rw [extension.agrees ⟨hB hw, hwU⟩,
      extension.agrees ⟨hB boundary.mem, extension.mem_neighborhood⟩, hzero, neg_zero]
    exact neg_nonpos.mpr (system.radius_nonneg w (hB hw))
  obtain ⟨coefficient, hnonneg, heq⟩ := boundary.exists_nonneg_smul_of_isLocalMaxOn
    _ _ hnegativeGradient hmax
  refine ⟨coefficient, hnonneg, ?_⟩
  have hnegative := congrArg Neg.neg heq
  simpa only [neg_neg, ← neg_smul] using hnegative

/-- Theorem 3.8's normal formula, derived from an actual contributor and recipient. -/
theorem SetValuedSystem.normalUpdate_eq_of_inflation_contact
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z : E)
    (source : C1BoundaryAt B y) (recipient : C1BoundaryAt (inflation system.radius B) z)
    (hcontact : dist z y = system.radius y) :
    normalUpdate (system.radiusGradientOnAmbient y) source.normal = recipient.normal := by
  by_cases hzero : system.radius y = 0
  · have hzy : z = y := dist_eq_zero.mp (hcontact.trans hzero)
    subst z
    have hcommon : source.normal = recipient.normal := source.normal_eq_of_subset recipient
      (subset_inflation system.radius B (fun w hw => system.radius_nonneg w (hB hw)))
    obtain ⟨coefficient, _, hgradient⟩ :=
      system.exists_nonpos_radiusGradient_smul_at_zero B hB y source hzero
    rw [hgradient, normalUpdate_smul_self _ _ source.normal_unit, hcommon]
  · have hpositive : 0 < system.radius y :=
      lt_of_le_of_ne (system.radius_nonneg y (hB source.mem)) (Ne.symm hzero)
    obtain ⟨coefficient, hnonneg, heq⟩ := system.exists_nonneg_contact_position_multiplier
      B hB y z source recipient.mem_frontier hcontact
    have hposition := recipient.position_eq_of_inflation_contact system.radius B y z
      source.mem hpositive.le hcontact
    apply normalUpdate_eq_of_nonneg_scaled_contact (system.radiusGradientOnAmbient y)
      source.normal recipient.normal
      (hcontraction.norm_radiusGradientOnAmbient y (hB source.mem)) source.normal_unit
      recipient.normal_unit (system.radius y) coefficient hpositive hnonneg
    have hradial : system.radius y • recipient.normal = z - y := by
      have hsubtract := congrArg (fun v : E => v - y) hposition
      simpa only [add_sub_cancel_left] using hsubtract.symm
    rw [hradial]
    exact heq

/-- The actual exponential formula carries the source normal pair to the recipient normal pair. -/
theorem SetValuedSystem.exponentialMap_of_inflation_contact
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z : E)
    (source : C1BoundaryAt B y) (recipient : C1BoundaryAt (inflation system.radius B) z)
    (hcontact : dist z y = system.radius y) :
    exponentialMap system.radius system.radiusGradientOnAmbient (y, source.normal) =
      (z, recipient.normal) := by
  have hnormal := system.normalUpdate_eq_of_inflation_contact hcontraction B hB y z
    source recipient hcontact
  apply Prod.ext
  · change y + system.radius y • normalUpdate (system.radiusGradientOnAmbient y) source.normal = z
    rw [hnormal]
    exact (recipient.position_eq_of_inflation_contact system.radius B y z source.mem
      (system.radius_nonneg y (hB source.mem)) hcontact).symm
  · exact hnormal

/-- The same conclusion in the genuine unit-normal bundle. -/
theorem SetValuedSystem.exponentialLift_of_inflation_contact
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z : E)
    (source : C1BoundaryAt B y) (recipient : C1BoundaryAt (inflation system.radius B) z)
    (hcontact : dist z y = system.radius y) :
    system.exponentialLift hcontraction
      (⟨y, hB source.mem⟩, ⟨source.normal, source.normal_unit⟩) =
      (z, ⟨recipient.normal, recipient.normal_unit⟩) := by
  have heq := system.exponentialMap_of_inflation_contact hcontraction B hB y z source recipient hcontact
  apply Prod.ext
  · exact congrArg (fun output : E × E => output.1) heq
  · exact Subtype.ext (congrArg Prod.snd heq)

/-- The explicit nonnegative multiplier in Theorem 3.8. -/
theorem SetValuedSystem.explicit_contact_multiplier_nonneg
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (y : E) (hy : y ∈ system.domain) (n : E) :
    0 ≤ system.radius y * (inner ℝ n (system.radiusGradientOnAmbient y) +
      Real.sqrt ((inner ℝ n (system.radiusGradientOnAmbient y)) ^ 2 -
        ‖system.radiusGradientOnAmbient y‖ ^ 2 + 1)) :=
  mul_nonneg (system.radius_nonneg y hy)
    (normalUpdate_coefficient_pos (system.radiusGradientOnAmbient y) n
      (hcontraction.norm_radiusGradientOnAmbient y hy)).le

/-- The explicit multiplier gives the stated centre-to-recipient position formula. -/
theorem SetValuedSystem.contact_position_eq_explicit_multiplier
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (B : Set E) (hB : B ⊆ system.domain) (y z : E)
    (source : C1BoundaryAt B y) (recipient : C1BoundaryAt (inflation system.radius B) z)
    (hcontact : dist z y = system.radius y) :
    z = y + (system.radius y * (inner ℝ source.normal (system.radiusGradientOnAmbient y) +
      Real.sqrt ((inner ℝ source.normal (system.radiusGradientOnAmbient y)) ^ 2 -
        ‖system.radiusGradientOnAmbient y‖ ^ 2 + 1))) • source.normal -
      system.radius y • system.radiusGradientOnAmbient y := by
  have hposition := recipient.position_eq_of_inflation_contact system.radius B y z source.mem
    (system.radius_nonneg y (hB source.mem)) hcontact
  rw [← system.normalUpdate_eq_of_inflation_contact hcontraction B hB y z source recipient hcontact,
    normalUpdate, smul_sub, smul_smul] at hposition
  exact hposition.trans (by abel)

end BoundedUncertainty
