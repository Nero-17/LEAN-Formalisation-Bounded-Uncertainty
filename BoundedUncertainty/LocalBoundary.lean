import BoundedUncertainty.Basic
import BoundedUncertainty.BoundaryNormalAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
Local C1 boundary data in regular-level-set form. The defining function is
nonpositive on the set and has unit gradient at the marked boundary point.
The normalization is justified below from any nonzero defining gradient.
No common-normal or multiplier conclusion is included in these data.
-/

namespace BoundedUncertainty

open Set Filter Topology

theorem eventually_pos_right_of_hasDerivAt {f : ℝ → ℝ} {derivative : ℝ}
    (hf : HasDerivAt f derivative 0) (hzero : f 0 = 0) (hpositive : 0 < derivative) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t := by
  have hlimit := hf.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hpositive)
  filter_upwards [hlimit, self_mem_nhdsWithin] with t ht htpos
  simp only [zero_add, hzero, sub_zero, smul_eq_mul] at ht
  exact pos_of_mul_pos_right ht (inv_nonneg.mpr (le_of_lt htpos))

theorem eventually_neg_right_of_hasDerivAt {f : ℝ → ℝ} {derivative : ℝ}
    (hf : HasDerivAt f derivative 0) (hzero : f 0 = 0) (hnegative : derivative < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < 0 := by
  have hpositive := eventually_pos_right_of_hasDerivAt hf.neg
    (by simp [hzero]) (neg_pos.mpr hnegative)
  simpa only [Pi.neg_apply, neg_pos] using hpositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Normalized local defining-function data for an outward C1 boundary. -/
structure C1BoundaryAt (B : Set E) (y : E) where
  neighborhood : Set E
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : y ∈ neighborhood
  defining : E → ℝ
  contDiffOn_defining : ContDiffOn ℝ 1 defining neighborhood
  defining_eq_zero : defining y = 0
  mem_iff : ∀ z ∈ neighborhood, z ∈ B ↔ defining z ≤ 0
  normal : E
  normal_unit : ‖normal‖ = 1
  hasGradientAt_defining : HasGradientAt defining normal y

/-- Any regular C1 defining function can be normalized to these boundary data. -/
noncomputable def C1BoundaryAt.ofDefiningFunction (B : Set E) (y : E)
    (U : Set E) (hU : IsOpen U) (hyU : y ∈ U) (defining : E → ℝ)
    (hsmooth : ContDiffOn ℝ 1 defining U) (hzero : defining y = 0)
    (hset : ∀ z ∈ U, z ∈ B ↔ defining z ≤ 0)
    (gradient : E) (hgradient : HasGradientAt defining gradient y)
    (hnonzero : gradient ≠ 0) : C1BoundaryAt B y where
  neighborhood := U
  isOpen_neighborhood := hU
  mem_neighborhood := hyU
  defining z := ‖gradient‖⁻¹ * defining z
  contDiffOn_defining := contDiffOn_const.mul hsmooth
  defining_eq_zero := by simp only [hzero, mul_zero]
  mem_iff z hz := by
    rw [hset z hz]
    constructor
    · exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg gradient))
    · intro hnonpos
      apply le_of_not_gt
      intro hpositive
      exact (not_lt_of_ge hnonpos)
        (mul_pos (inv_pos.mpr (norm_pos_iff.mpr hnonzero)) hpositive)
  normal := ‖gradient‖⁻¹ • gradient
  normal_unit := norm_smul_inv_norm hnonzero
  hasGradientAt_defining := by
    rw [hasGradientAt_iff_hasFDerivAt, map_smul]
    exact hgradient.hasFDerivAt.const_smul ‖gradient‖⁻¹

theorem C1BoundaryAt.mem {B : Set E} {y : E} (boundary : C1BoundaryAt B y) : y ∈ B :=
  (boundary.mem_iff y boundary.mem_neighborhood).mpr boundary.defining_eq_zero.le

theorem C1BoundaryAt.hasDerivAt_defining_ray {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) (v : E) :
    HasDerivAt (fun t : ℝ => boundary.defining (y + t • v))
      (inner ℝ boundary.normal v) 0 := by
  have hcomp := boundary.hasGradientAt_defining.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y) (by simp)
  simpa only [zero_smul, add_zero, one_smul, InnerProductSpace.toDual_apply_apply] using hcomp

/-- A direction making an acute angle with the inward normal enters the set. -/
theorem C1BoundaryAt.eventually_mem_ray_of_inner_neg {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) (v : E) (hv : inner ℝ boundary.normal v < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • v ∈ B := by
  have hnegative := eventually_neg_right_of_hasDerivAt (boundary.hasDerivAt_defining_ray v)
    (by simpa using boundary.defining_eq_zero) hv
  have hcontinuous : Continuous (fun t : ℝ => y + t • v) := by fun_prop
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), y + t • v ∈ boundary.neighborhood :=
    hcontinuous.continuousAt.preimage_mem_nhds (by
      simpa using boundary.isOpen_neighborhood.mem_nhds boundary.mem_neighborhood)
  filter_upwards [hnegative, hnear.filter_mono nhdsWithin_le_nhds] with t ht htU
  exact (boundary.mem_iff _ htU).mpr ht.le

theorem C1BoundaryAt.eventually_not_mem_ray_of_inner_pos {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) (v : E) (hv : 0 < inner ℝ boundary.normal v) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), y + t • v ∉ B := by
  have hpositive := eventually_pos_right_of_hasDerivAt (boundary.hasDerivAt_defining_ray v)
    (by simpa using boundary.defining_eq_zero) hv
  have hcontinuous : Continuous (fun t : ℝ => y + t • v) := by fun_prop
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), y + t • v ∈ boundary.neighborhood :=
    hcontinuous.continuousAt.preimage_mem_nhds (by
      simpa using boundary.isOpen_neighborhood.mem_nhds boundary.mem_neighborhood)
  filter_upwards [hpositive, hnear.filter_mono nhdsWithin_le_nhds] with t ht htU htB
  exact (not_le_of_gt ht) ((boundary.mem_iff _ htU).mp htB)

theorem C1BoundaryAt.mem_posTangentConeAt_of_inner_neg {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) (v : E) (hv : inner ℝ boundary.normal v < 0) :
    v ∈ posTangentConeAt B y :=
  mem_posTangentConeAt_of_frequently_mem
    (boundary.eventually_mem_ray_of_inner_neg v hv).frequently

/-- An actual local maximum over the set has nonpositive derivatives in inward directions. -/
theorem C1BoundaryAt.inner_gradient_nonpos_of_isLocalMaxOn {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) (f : E → ℝ) (gradient : E)
    (hf : HasGradientAt f gradient y) (hmax : IsLocalMaxOn f B y)
    (v : E) (hv : inner ℝ boundary.normal v < 0) : inner ℝ gradient v ≤ 0 := by
  exact hmax.hasFDerivWithinAt_nonpos hf.hasFDerivAt.hasFDerivWithinAt
    (boundary.mem_posTangentConeAt_of_inner_neg v hv)

/-- The defining-function data really mark a frontier point. -/
theorem C1BoundaryAt.mem_frontier {B : Set E} {y : E} (boundary : C1BoundaryAt B y) :
    y ∈ frontier B := by
  refine ⟨subset_closure boundary.mem, ?_⟩
  intro hyint
  have houtside := boundary.eventually_not_mem_ray_of_inner_pos boundary.normal (by
    simp only [real_inner_self_eq_norm_sq, boundary.normal_unit, one_pow]
    exact zero_lt_one)
  have hcontinuous : Continuous (fun t : ℝ => y + t • boundary.normal) := by fun_prop
  have hinside : ∀ᶠ t in 𝓝 (0 : ℝ), y + t • boundary.normal ∈ B :=
    hcontinuous.continuousAt.preimage_mem_nhds (by
      simpa using mem_interior_iff_mem_nhds.mp hyint)
  exact ((hinside.filter_mono nhdsWithin_le_nhds).and houtside).exists.elim
    (fun _ h => h.2 h.1)

/-- Lemma 3.5: nested sets with outward C1 boundary data have the same normal. -/
theorem C1BoundaryAt.normal_eq_of_subset {B C : Set E} {y : E}
    (innerBoundary : C1BoundaryAt B y) (outerBoundary : C1BoundaryAt C y)
    (hBC : B ⊆ C) : innerBoundary.normal = outerBoundary.normal := by
  apply unit_normals_eq_of_halfspace_nonpos innerBoundary.normal outerBoundary.normal
    innerBoundary.normal_unit outerBoundary.normal_unit
  intro v hv
  apply le_of_not_gt
  intro hpositive
  have hinside := innerBoundary.eventually_mem_ray_of_inner_neg v hv
  have houtside := outerBoundary.eventually_not_mem_ray_of_inner_pos v hpositive
  exact (hinside.and houtside).exists.elim (fun _ h => h.2 (hBC h.1))

/-- The outward normal is independent of the chosen normalized defining function. -/
theorem C1BoundaryAt.normal_unique {B : Set E} {y : E}
    (first second : C1BoundaryAt B y) : first.normal = second.normal :=
  first.normal_eq_of_subset second Subset.rfl

/-- The local maximum multiplier, with its sign, is derived from inward directions. -/
theorem C1BoundaryAt.exists_nonneg_smul_of_isLocalMaxOn {B : Set E} {y : E}
    (boundary : C1BoundaryAt B y) (f : E → ℝ) (gradient : E)
    (hf : HasGradientAt f gradient y) (hmax : IsLocalMaxOn f B y) :
    ∃ coefficient : ℝ, 0 ≤ coefficient ∧ gradient = coefficient • boundary.normal :=
  exists_nonneg_smul_of_halfspace_nonpos boundary.normal gradient boundary.normal_unit
    (boundary.inner_gradient_nonpos_of_isLocalMaxOn f gradient hf hmax)

end BoundedUncertainty
