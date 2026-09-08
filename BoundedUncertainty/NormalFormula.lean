import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# The normal update in Definition 3.9 and Proposition 3.10

This module proves the algebraic well-definedness of the manuscript's normal
formula. The vector `gradient` stands for the gradient of the radius at the
centre. The strict contraction bound is an explicit hypothesis, including when
the radius itself is zero. No differentiability or positive-radius hypothesis
is needed for this algebraic part.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The output normal from Definition 3.9. -/
noncomputable def normalUpdate (gradient n : E) : E :=
  (inner ℝ n gradient +
    Real.sqrt ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1)) • n - gradient

/-- The full lower-bound inequality displayed in Proposition 3.10. -/
theorem normalUpdate_radicand_bounds (gradient n : E) (hgradient : ‖gradient‖ < 1) :
    1 - ‖gradient‖ ^ 2 ≤ (inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1 ∧
      0 < 1 - ‖gradient‖ ^ 2 := by
  constructor
  · nlinarith [sq_nonneg (inner ℝ n gradient)]
  · nlinarith [norm_nonneg gradient]

theorem normalUpdate_radicand_pos (gradient n : E) (hgradient : ‖gradient‖ < 1) :
    0 < (inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1 := by
  nlinarith [norm_nonneg gradient, sq_nonneg (inner ℝ n gradient)]

theorem normalUpdate_coefficient_pos (gradient n : E) (hgradient : ‖gradient‖ < 1) :
    0 < inner ℝ n gradient +
      Real.sqrt ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1) := by
  have hsqrt := Real.sq_sqrt (le_of_lt (normalUpdate_radicand_pos gradient n hgradient))
  have hnonneg := Real.sqrt_nonneg ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1)
  nlinarith [norm_nonneg gradient]

/-- Proposition 3.10: the normal formula takes unit vectors to unit vectors. -/
theorem norm_normalUpdate (gradient n : E) (hgradient : ‖gradient‖ < 1)
    (hn : ‖n‖ = 1) : ‖normalUpdate gradient n‖ = 1 := by
  have hsqrt := Real.sq_sqrt (le_of_lt (normalUpdate_radicand_pos gradient n hgradient))
  have hcoefficient := normalUpdate_coefficient_pos gradient n hgradient
  have hnorm := norm_sub_sq_real
    ((inner ℝ n gradient +
      Real.sqrt ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1)) • n) gradient
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcoefficient, hn,
    real_inner_smul_left] at hnorm
  change ‖normalUpdate gradient n‖ ^ 2 = _ at hnorm
  nlinarith [norm_nonneg (normalUpdate gradient n)]

/-- The inverse direction is obtained by normalizing the output plus the gradient. -/
theorem normalize_normalUpdate_add_gradient (gradient n : E)
    (hgradient : ‖gradient‖ < 1) (hn : ‖n‖ = 1) :
    ‖normalUpdate gradient n + gradient‖⁻¹ •
      (normalUpdate gradient n + gradient) = n := by
  have hcoefficient := normalUpdate_coefficient_pos gradient n hgradient
  simp only [normalUpdate, sub_add_cancel, norm_smul, Real.norm_eq_abs,
    abs_of_pos hcoefficient, hn, mul_one, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hcoefficient), one_smul]

/-- At a fixed gradient the normal update is injective on the unit sphere. -/
theorem normalUpdate_inj (gradient n₁ n₂ : E) (hgradient : ‖gradient‖ < 1)
    (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (heq : normalUpdate gradient n₁ = normalUpdate gradient n₂) : n₁ = n₂ := by
  rw [← normalize_normalUpdate_add_gradient gradient n₁ hgradient hn₁,
    heq, normalize_normalUpdate_add_gradient gradient n₂ hgradient hn₂]

/-- The positive solution of the unit-normal quadratic is the stated coefficient. -/
theorem normalUpdate_coefficient_unique (gradient n : E)
    (hgradient : ‖gradient‖ < 1) (hn : ‖n‖ = 1)
    (t : ℝ) (ht : 0 < t) (hunit : ‖t • n - gradient‖ = 1) :
    t = inner ℝ n gradient +
      Real.sqrt ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1) := by
  have hsqrt := Real.sq_sqrt (le_of_lt (normalUpdate_radicand_pos gradient n hgradient))
  have hnegative := normalUpdate_coefficient_pos gradient (-n) hgradient
  simp only [inner_neg_left, neg_sq] at hnegative
  have hnorm := norm_sub_sq_real (t • n) gradient
  rw [hunit, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hn,
    real_inner_smul_left] at hnorm
  have hfactor :
      (t - (inner ℝ n gradient +
        Real.sqrt ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1))) *
      (t + Real.sqrt ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1) -
        inner ℝ n gradient) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

omit [InnerProductSpace ℝ E] in
theorem unit_add_gradient_ne_zero (gradient u : E)
    (hgradient : ‖gradient‖ < 1) (hu : ‖u‖ = 1) : u + gradient ≠ 0 := by
  intro heq
  have : gradient = -u := eq_neg_of_add_eq_zero_right heq
  rw [this, norm_neg, hu] at hgradient
  exact (lt_irrefl (1 : ℝ)) hgradient

/-- The explicit inverse direction is itself a unit vector. -/
theorem norm_normalize_unit_add_gradient (gradient u : E)
    (hgradient : ‖gradient‖ < 1) (hu : ‖u‖ = 1) :
    ‖‖u + gradient‖⁻¹ • (u + gradient)‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (unit_add_gradient_ne_zero gradient u hgradient hu))]

/-- The inverse formula also recovers every prescribed unit output normal. -/
theorem normalUpdate_normalize_add_gradient (gradient u : E)
    (hgradient : ‖gradient‖ < 1) (hu : ‖u‖ = 1) :
    normalUpdate gradient (‖u + gradient‖⁻¹ • (u + gradient)) = u := by
  have hnonzero := norm_ne_zero_iff.mpr (unit_add_gradient_ne_zero gradient u hgradient hu)
  have hcancel :
      ‖u + gradient‖ • (‖u + gradient‖⁻¹ • (u + gradient)) - gradient = u := by
    rw [smul_smul, mul_inv_cancel₀ hnonzero, one_smul, add_sub_cancel_right]
  have hcoefficient := normalUpdate_coefficient_unique gradient
    (‖u + gradient‖⁻¹ • (u + gradient)) hgradient
    (norm_normalize_unit_add_gradient gradient u hgradient hu)
    ‖u + gradient‖ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnonzero))
    (by rw [hcancel, hu])
  unfold normalUpdate
  rw [← hcoefficient]
  exact hcancel

/-- The normal formula and its explicit inverse give an equivalence of unit spheres. -/
noncomputable def normalSphereEquiv (gradient : E) (hgradient : ‖gradient‖ < 1) :
    {n : E // ‖n‖ = 1} ≃ {u : E // ‖u‖ = 1} where
  toFun n := ⟨normalUpdate gradient n, norm_normalUpdate gradient n hgradient n.property⟩
  invFun u := ⟨‖(u : E) + gradient‖⁻¹ • ((u : E) + gradient),
    norm_normalize_unit_add_gradient gradient u hgradient u.property⟩
  left_inv n := Subtype.ext
    (normalize_normalUpdate_add_gradient gradient n hgradient n.property)
  right_inv u := Subtype.ext
    (normalUpdate_normalize_add_gradient gradient u hgradient u.property)

/-- Joint continuity of the displayed algebraic normal formula. -/
theorem continuous_normalUpdate :
    Continuous (fun p : E × E => normalUpdate p.1 p.2) := by
  unfold normalUpdate
  fun_prop

/-- The fixed-gradient normal correspondence is a homeomorphism of unit spheres.
This is only the normal-coordinate part of the boundary map, not Theorem 3.14. -/
noncomputable def normalSphereHomeomorph (gradient : E) (hgradient : ‖gradient‖ < 1) :
    {n : E // ‖n‖ = 1} ≃ₜ {u : E // ‖u‖ = 1} where
  toEquiv := normalSphereEquiv gradient hgradient
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_normalUpdate.comp (continuous_const.prodMk continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.smul
    · apply Continuous.inv₀
      · exact (continuous_subtype_val.add continuous_const).norm
      · intro u
        exact norm_ne_zero_iff.mpr
          (unit_add_gradient_ne_zero gradient u hgradient u.property)
    · exact continuous_subtype_val.add continuous_const

end BoundedUncertainty
