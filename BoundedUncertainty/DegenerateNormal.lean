import BoundedUncertainty.NormalFormula

/-! Remark 3.16: the exact nonnegative-radicand condition suffices for
the algebraic output to be a unit vector, even without strict contraction. -/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_normalUpdate_of_radicand_nonneg (gradient n : E) (hn : ‖n‖ = 1)
    (hradicand : 0 ≤ (inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1) :
    ‖normalUpdate gradient n‖ = 1 := by
  have hsqrt := Real.sq_sqrt hradicand
  have hnorm := norm_sub_sq_real
    ((inner ℝ n gradient +
      Real.sqrt ((inner ℝ n gradient) ^ 2 - ‖gradient‖ ^ 2 + 1)) • n) gradient
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hn, one_pow, mul_one,
    real_inner_smul_left] at hnorm
  change ‖normalUpdate gradient n‖ ^ 2 = _ at hnorm
  nlinarith [norm_nonneg (normalUpdate gradient n)]

theorem normalUpdate_ne_self_of_orthogonal (gradient n : E)
    (hgradient : gradient ≠ 0) (horthogonal : inner ℝ n gradient = 0) :
    normalUpdate gradient n ≠ n := by
  intro heq
  have hinner := congrArg (fun v : E => inner ℝ v gradient) heq
  simp only [normalUpdate, inner_sub_left, real_inner_smul_left, horthogonal,
    mul_zero, zero_sub, real_inner_self_eq_norm_sq] at hinner
  have hnorm := norm_pos_iff.mpr hgradient
  nlinarith

end BoundedUncertainty
