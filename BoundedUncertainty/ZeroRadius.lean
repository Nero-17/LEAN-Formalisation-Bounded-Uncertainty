import BoundedUncertainty.BoundaryMap
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The zero-radius local minimum argument

This module supplies the analytic step used when a nonnegative smooth radius
vanishes at an interior point. The local-minimum hypothesis is an ambient
one. Nonnegativity only on a set with boundary does not establish that
hypothesis for its ambient extension.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
theorem normalUpdate_zero_gradient (n : E) : normalUpdate (0 : E) n = n := by
  simp [normalUpdate]

variable [CompleteSpace E]

/-- Fermat's theorem expressed as an actual gradient statement. -/
theorem hasGradientAt_zero_of_isLocalMin (f : E → ℝ) (y : E)
    (hmin : IsLocalMin f y) (hdiff : DifferentiableAt ℝ f y) :
    HasGradientAt f 0 y := by
  rw [hasGradientAt_iff_hasFDerivAt, map_zero]
  simpa only [hmin.fderiv_eq_zero] using hdiff.hasFDerivAt

theorem gradient_eq_zero_of_isLocalMin (f : E → ℝ) (y : E)
    (hmin : IsLocalMin f y) (hdiff : DifferentiableAt ℝ f y) :
    gradient f y = 0 :=
  (hasGradientAt_zero_of_isLocalMin f y hmin hdiff).gradient

/-- Local nonnegativity is sufficient when the function vanishes. -/
theorem gradient_eq_zero_of_eventually_nonneg (f : E → ℝ) (y : E)
    (hnonneg : ∀ᶠ z in nhds y, 0 ≤ f z) (hzero : f y = 0)
    (hdiff : DifferentiableAt ℝ f y) : gradient f y = 0 := by
  apply gradient_eq_zero_of_isLocalMin f y _ hdiff
  show ∀ᶠ z in nhds y, f y ≤ f z
  simpa only [hzero] using hnonneg

theorem normalUpdate_gradient_of_isLocalMin (f : E → ℝ) (y n : E)
    (hmin : IsLocalMin f y) (hdiff : DifferentiableAt ℝ f y) :
    normalUpdate (gradient f y) n = n := by
  rw [gradient_eq_zero_of_isLocalMin f y hmin hdiff, normalUpdate_zero_gradient]

/-- At an ambient local minimum with zero radius, both lift coordinates are fixed. -/
theorem exponentialMap_of_zero_radius_of_isLocalMin (f : E → ℝ) (y n : E)
    (hmin : IsLocalMin f y) (hdiff : DifferentiableAt ℝ f y) (hzero : f y = 0) :
    exponentialMap f (gradient f) (y, n) = (y, n) := by
  simp [exponentialMap, hzero, gradient_eq_zero_of_isLocalMin f y hmin hdiff]

theorem exponentialMap_of_zero_radius_of_eventually_nonneg (f : E → ℝ) (y n : E)
    (hnonneg : ∀ᶠ z in nhds y, 0 ≤ f z) (hzero : f y = 0)
    (hdiff : DifferentiableAt ℝ f y) :
    exponentialMap f (gradient f) (y, n) = (y, n) := by
  simp [exponentialMap, hzero,
    gradient_eq_zero_of_eventually_nonneg f y hnonneg hzero hdiff]

variable {r s : ℕ}

/-- The canonical radius gradient vanishes at every interior zero-radius centre.
Nonnegativity is transferred to a local extension only near this interior point. -/
theorem SetValuedSystem.radiusGradient_eq_zero_of_mem_interior
    (system : SetValuedSystem (E := E) r s) (y : system.domain)
    (hy : (y : E) ∈ interior system.domain) (hzero : system.radius y = 0) :
    system.radiusGradient y = 0 := by
  obtain ⟨extension⟩ := system.radius_extension y y.property
  rw [system.radiusGradient_eq_extension system.radius_order_pos extension y
    extension.mem_neighborhood]
  apply gradient_eq_zero_of_eventually_nonneg extension.extension y
  · filter_upwards
      [extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood,
        isOpen_interior.mem_nhds hy] with z hzU hzX
    rw [extension.agrees ⟨interior_subset hzX, hzU⟩]
    exact system.radius_nonneg z (interior_subset hzX)
  · exact (extension.agrees ⟨y.property, extension.mem_neighborhood⟩).trans hzero
  · have hcontdiff : ContDiffOn ℝ 1 extension.extension extension.neighborhood :=
      extension.contDiffOn_extension.of_le (by exact_mod_cast system.radius_order_pos)
    exact hcontdiff.differentiableOn_one.differentiableAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)

/-- Proposition 3.15's zero-gradient conclusion on the whole state space. -/
theorem SetValuedSystem.radiusGradient_eq_zero_of_domain_eq_univ
    (system : SetValuedSystem (E := E) r s) (hX : system.domain = Set.univ)
    (y : system.domain) (hzero : system.radius y = 0) :
    system.radiusGradient y = 0 :=
  system.radiusGradient_eq_zero_of_mem_interior y (by simp [hX]) hzero

/-- The actual radius-gradient formula fixes an interior zero-radius centre and its normal.
No contraction bound away from this centre is needed for this identity. -/
theorem SetValuedSystem.exponentialMap_of_zero_radius_of_mem_interior
    (system : SetValuedSystem (E := E) r s) (y : system.domain) (n : E)
    (hy : (y : E) ∈ interior system.domain) (hzero : system.radius y = 0) :
    exponentialMap system.radius system.radiusGradientOnAmbient ((y : E), n) =
      ((y : E), n) := by
  simp [exponentialMap, hzero,
    system.radiusGradient_eq_zero_of_mem_interior y hy hzero]

/-- Proposition 3.15's fixed-pair conclusion, with the canonical radius gradient. -/
theorem SetValuedSystem.exponentialMap_of_zero_radius_of_domain_eq_univ
    (system : SetValuedSystem (E := E) r s) (hX : system.domain = Set.univ)
    (y : system.domain) (n : E) (hzero : system.radius y = 0) :
    exponentialMap system.radius system.radiusGradientOnAmbient ((y : E), n) =
      ((y : E), n) :=
  system.exponentialMap_of_zero_radius_of_mem_interior y n (by simp [hX]) hzero

theorem SetValuedSystem.exponentialLift_of_zero_radius_of_mem_interior
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (y : system.domain) (n : {n : E // ‖n‖ = 1})
    (hy : (y : E) ∈ interior system.domain) (hzero : system.radius y = 0) :
    system.exponentialLift hcontraction (y, n) = ((y : E), n) := by
  apply Prod.ext
  · change (exponentialMap system.radius system.radiusGradientOnAmbient ((y : E), n)).1 = y
    rw [system.exponentialMap_of_zero_radius_of_mem_interior y n hy hzero]
  · apply Subtype.ext
    change (exponentialMap system.radius system.radiusGradientOnAmbient ((y : E), n)).2 = n
    rw [system.exponentialMap_of_zero_radius_of_mem_interior y n hy hzero]

theorem SetValuedSystem.exponentialLift_of_zero_radius_of_domain_eq_univ
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (hX : system.domain = Set.univ) (y : system.domain) (n : {n : E // ‖n‖ = 1})
    (hzero : system.radius y = 0) :
    system.exponentialLift hcontraction (y, n) = ((y : E), n) :=
  system.exponentialLift_of_zero_radius_of_mem_interior hcontraction y n (by simp [hX]) hzero

end BoundedUncertainty
