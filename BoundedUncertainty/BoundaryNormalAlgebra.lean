import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Algebra of supporting halfspaces

These results isolate the linear-algebra step needed by the common-normal and
constrained-extremum arguments in Section 3. Only a real inner product and a
unit normal are assumed. No dimension, boundary regularity, or geometric
conclusion is included in the hypotheses.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A functional nonpositive on an open negative halfspace is also nonpositive
on directions orthogonal to its unit normal. The proof uses an explicit direction. -/
theorem inner_nonpos_of_halfspace_nonpos_of_orthogonal (n g v : E) (hn : ‖n‖ = 1)
    (hhalfspace : ∀ w : E, inner ℝ n w < 0 → inner ℝ g w ≤ 0)
    (horthogonal : inner ℝ n v = 0) : inner ℝ g v ≤ 0 := by
  apply le_of_not_gt
  intro hpositive
  have hnegative :
      inner ℝ n ((1 + inner ℝ g n) • v - (inner ℝ g v) • n) < 0 := by
    simp only [inner_sub_right, real_inner_smul_right, horthogonal,
      real_inner_self_eq_norm_sq, hn, one_pow, mul_zero, mul_one, zero_sub]
    exact neg_neg_of_pos hpositive
  have hnonpos := hhalfspace
    ((1 + inner ℝ g n) • v - (inner ℝ g v) • n) hnegative
  simp only [inner_sub_right, real_inner_smul_right] at hnonpos
  nlinarith

/-- Every tangent direction is annihilated by the supporting functional. -/
theorem inner_eq_zero_of_halfspace_nonpos_of_orthogonal (n g v : E) (hn : ‖n‖ = 1)
    (hhalfspace : ∀ w : E, inner ℝ n w < 0 → inner ℝ g w ≤ 0)
    (horthogonal : inner ℝ n v = 0) : inner ℝ g v = 0 := by
  apply le_antisymm
  · exact inner_nonpos_of_halfspace_nonpos_of_orthogonal n g v hn hhalfspace horthogonal
  · have hnegative := inner_nonpos_of_halfspace_nonpos_of_orthogonal n g (-v) hn hhalfspace
      (by simp only [inner_neg_right, horthogonal, neg_zero])
    simpa only [inner_neg_right, neg_nonpos] using hnegative

theorem inner_nonneg_of_halfspace_nonpos (n g : E) (hn : ‖n‖ = 1)
    (hhalfspace : ∀ v : E, inner ℝ n v < 0 → inner ℝ g v ≤ 0) :
    0 ≤ inner ℝ g n := by
  have hnegative : inner ℝ n (-n) < 0 := by
    simp only [inner_neg_right, real_inner_self_eq_norm_sq, hn, one_pow]
    norm_num
  have hnonpos := hhalfspace (-n) hnegative
  simpa only [inner_neg_right, neg_nonpos] using hnonpos

/-- The supporting functional is a multiple of the unit normal, with an explicit coefficient. -/
theorem eq_inner_smul_of_halfspace_nonpos (n g : E) (hn : ‖n‖ = 1)
    (hhalfspace : ∀ v : E, inner ℝ n v < 0 → inner ℝ g v ≤ 0) :
    g = (inner ℝ g n) • n := by
  apply ext_inner_right ℝ
  intro v
  rw [real_inner_smul_left]
  have horthogonal : inner ℝ n (v - (inner ℝ n v) • n) = 0 := by
    simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hn, one_pow, mul_one, sub_self]
  have hzero := inner_eq_zero_of_halfspace_nonpos_of_orthogonal n g
    (v - (inner ℝ n v) • n) hn hhalfspace horthogonal
  simp only [inner_sub_right, real_inner_smul_right] at hzero
  exact (sub_eq_zero.mp hzero).trans (mul_comm _ _)

theorem exists_nonneg_smul_of_halfspace_nonpos (n g : E) (hn : ‖n‖ = 1)
    (hhalfspace : ∀ v : E, inner ℝ n v < 0 → inner ℝ g v ≤ 0) :
    ∃ coefficient : ℝ, 0 ≤ coefficient ∧ g = coefficient • n :=
  ⟨inner ℝ g n, inner_nonneg_of_halfspace_nonpos n g hn hhalfspace,
    eq_inner_smul_of_halfspace_nonpos n g hn hhalfspace⟩

/-- Inclusion of the corresponding inward halfspaces identifies two unit normals. -/
theorem unit_normals_eq_of_halfspace_nonpos (n₁ n₂ : E) (hn₁ : ‖n₁‖ = 1)
    (hn₂ : ‖n₂‖ = 1)
    (hhalfspace : ∀ v : E, inner ℝ n₁ v < 0 → inner ℝ n₂ v ≤ 0) : n₁ = n₂ := by
  have hcoefficient := inner_nonneg_of_halfspace_nonpos n₁ n₂ hn₁ hhalfspace
  have heq := eq_inner_smul_of_halfspace_nonpos n₁ n₂ hn₁ hhalfspace
  have hnorm := congrArg norm heq
  rw [hn₂, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoefficient, hn₁, mul_one] at hnorm
  rw [← hnorm, one_smul] at heq
  exact heq.symm

end BoundedUncertainty
