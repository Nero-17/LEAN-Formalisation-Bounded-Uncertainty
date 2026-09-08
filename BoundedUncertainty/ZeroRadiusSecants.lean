import BoundedUncertainty.BoundaryNormalContinuity
import BoundedUncertainty.ContributorFormula
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Two-moving-point tangent flatness at a zero-radius source boundary point.
Strict differentiability controls differences between arbitrary nearby pairs.
The ambient radius gradient may be a nonzero normal; only its tangential
component vanishes.
-/

namespace BoundedUncertainty

open Set Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A C1 defining function controls all two-point source secants near its marked point. -/
theorem C1BoundaryAt.isLittleO_normal_chord
    {B : Set E} {y : E} (boundary : C1BoundaryAt B y) (hclosed : IsClosed B)
    (first second : ℕ → E) (hfirst : Tendsto first atTop (𝓝 y))
    (hsecond : Tendsto second atTop (𝓝 y))
    (hfirstFrontier : ∀ k, first k ∈ frontier B)
    (hsecondFrontier : ∀ k, second k ∈ frontier B) :
    (fun k => inner ℝ boundary.normal (second k - first k)) =o[atTop]
      (fun k => second k - first k) := by
  have hsmooth : ContDiffAt ℝ 1 boundary.defining y :=
    boundary.contDiffOn_defining.contDiffAt
      (boundary.isOpen_neighborhood.mem_nhds boundary.mem_neighborhood)
  have hstrict := hsmooth.hasStrictFDerivAt' boundary.hasGradientAt_defining.hasFDerivAt one_ne_zero
  have hsmall := hstrict.isLittleO.comp_tendsto (hsecond.prodMk_nhds hfirst)
  apply hsmall.neg_left.congr' _ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hfirst.eventually
    (boundary.isOpen_neighborhood.mem_nhds boundary.mem_neighborhood),
    hsecond.eventually (boundary.isOpen_neighborhood.mem_nhds boundary.mem_neighborhood)]
    with k hkfirst hksecond
  have hfirstZero := boundary.defining_eq_zero_of_mem_frontier (hfirstFrontier k)
    (hclosed.frontier_subset (hfirstFrontier k)) hkfirst
  have hsecondZero := boundary.defining_eq_zero_of_mem_frontier (hsecondFrontier k)
    (hclosed.frontier_subset (hsecondFrontier k)) hksecond
  simp only [Function.comp_apply, hfirstZero, hsecondZero, sub_self, zero_sub, neg_neg,
    InnerProductSpace.toDual_apply_apply]

theorem C1BoundaryAt.tendsto_normalized_normal_chord
    {B : Set E} {y : E} (boundary : C1BoundaryAt B y) (hclosed : IsClosed B)
    (first second : ℕ → E) (hfirst : Tendsto first atTop (𝓝 y))
    (hsecond : Tendsto second atTop (𝓝 y))
    (hfirstFrontier : ∀ k, first k ∈ frontier B)
    (hsecondFrontier : ∀ k, second k ∈ frontier B) :
    Tendsto (fun k => |inner ℝ boundary.normal (second k - first k)| /
      ‖second k - first k‖) atTop (𝓝 0) := by
  simpa only [Real.norm_eq_abs] using
    (boundary.isLittleO_normal_chord hclosed first second hfirst hsecond
      hfirstFrontier hsecondFrontier).norm_norm.tendsto_div_nhds_zero

variable {r s : ℕ}

/-- The radius difference is little-o of the moving source chord at a zero-radius point. -/
theorem SetValuedSystem.isLittleO_radius_difference_at_zero
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (hclosed : IsClosed B) (y : E) (boundary : C1BoundaryAt B y)
    (hzero : system.radius y = 0)
    (first second : ℕ → E) (hfirst : Tendsto first atTop (𝓝 y))
    (hsecond : Tendsto second atTop (𝓝 y))
    (hfirstFrontier : ∀ k, first k ∈ frontier B)
    (hsecondFrontier : ∀ k, second k ∈ frontier B) :
    (fun k => system.radius (second k) - system.radius (first k)) =o[atTop]
      (fun k => second k - first k) := by
  obtain ⟨coefficient, _, hparallel⟩ :=
    system.exists_nonpos_radiusGradient_smul_at_zero B hB y boundary hzero
  obtain ⟨extension⟩ := system.radius_extension y (hB boundary.mem)
  have hsmooth : ContDiffAt ℝ 1 extension.extension y :=
    (extension.contDiffOn_extension.of_le (by exact_mod_cast system.radius_order_pos)).contDiffAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  have hgradient : HasGradientAt extension.extension (system.radiusGradientOnAmbient y) y := by
    rw [(system.radiusGradientOnAmbient_apply ⟨y, hB boundary.mem⟩).trans
      (system.radiusGradient_eq_extension system.radius_order_pos extension
        ⟨y, hB boundary.mem⟩ extension.mem_neighborhood)]
    exact (hsmooth.differentiableAt one_ne_zero).hasGradientAt
  have hsmall := (hsmooth.hasStrictFDerivAt' hgradient.hasFDerivAt one_ne_zero).isLittleO.comp_tendsto
    (hsecond.prodMk_nhds hfirst)
  have hlinear :
      (fun k => InnerProductSpace.toDual ℝ E (system.radiusGradientOnAmbient y)
        (second k - first k)) =o[atTop] (fun k => second k - first k) := by
    simpa [InnerProductSpace.toDual_apply_apply, hparallel] using
      (boundary.isLittleO_normal_chord hclosed first second hfirst hsecond
        hfirstFrontier hsecondFrontier).const_mul_left (-coefficient)
  apply (hsmall.add hlinear).congr' _ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hfirst.eventually
    (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood),
    hsecond.eventually (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)]
    with k hkfirst hksecond
  have hfirstValue := extension.agrees
    ⟨hB (hclosed.frontier_subset (hfirstFrontier k)), hkfirst⟩
  have hsecondValue := extension.agrees
    ⟨hB (hclosed.frontier_subset (hsecondFrontier k)), hksecond⟩
  dsimp only [Function.comp_apply]
  rw [hfirstValue, hsecondValue]
  ring

theorem SetValuedSystem.tendsto_normalized_radius_difference_at_zero
    (system : SetValuedSystem (E := E) r s) (B : Set E) (hB : B ⊆ system.domain)
    (hclosed : IsClosed B) (y : E) (boundary : C1BoundaryAt B y)
    (hzero : system.radius y = 0)
    (first second : ℕ → E) (hfirst : Tendsto first atTop (𝓝 y))
    (hsecond : Tendsto second atTop (𝓝 y))
    (hfirstFrontier : ∀ k, first k ∈ frontier B)
    (hsecondFrontier : ∀ k, second k ∈ frontier B) :
    Tendsto (fun k => |system.radius (second k) - system.radius (first k)| /
      ‖second k - first k‖) atTop (𝓝 0) := by
  simpa only [Real.norm_eq_abs] using
    (system.isLittleO_radius_difference_at_zero B hB hclosed y boundary hzero
      first second hfirst hsecond hfirstFrontier hsecondFrontier).norm_norm.tendsto_div_nhds_zero

end BoundedUncertainty
