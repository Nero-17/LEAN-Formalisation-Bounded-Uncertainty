import BoundedUncertainty.ContributorFormula
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Positivity

/-! Remark 3.18, with a concrete counterexample satisfying every system
hypothesis except dimension at least two: X=[-1,1], f=id,
radius(x)=(1-x^2)/2. The gradient reaches magnitude one at the endpoints,
but both branches of the boundary formula are bijections of the interval. -/

namespace BoundedUncertainty

open Set

noncomputable def intervalRadius (x : ℝ) : ℝ := (1 - x ^ 2) / 2

theorem contDiff_intervalRadius (order : WithTop ℕ∞) :
    ContDiff ℝ order intervalRadius := by
  unfold intervalRadius
  fun_prop

theorem hasDerivAt_intervalRadius (x : ℝ) : HasDerivAt intervalRadius (-x) x := by
  convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).div_const 2 using 1
  dsimp
  ring

theorem hasGradientAt_intervalRadius (x : ℝ) : HasGradientAt intervalRadius (-x) x :=
  (hasDerivAt_intervalRadius x).hasGradientAt'

theorem intervalRadius_bounds (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ intervalRadius x ∧ intervalRadius x ≤ 1 / 2 := by
  dsimp [intervalRadius]
  constructor <;> nlinarith [sq_nonneg x, mul_nonneg (by linarith [hx.2] : 0 ≤ 1 - x)
    (by linarith [hx.1] : 0 ≤ 1 + x)]

theorem intervalRadius_ball_subset (x : ℝ) (_hx : x ∈ Icc (-1 : ℝ) 1) :
    Metric.closedBall x (intervalRadius x) ⊆ Icc (-1 : ℝ) 1 := by
  intro z hz
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hz
  dsimp [intervalRadius] at hz
  constructor <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]

theorem real_unit_cases (n : ℝ) (hn : ‖n‖ = 1) : n = 1 ∨ n = -1 := by
  rw [Real.norm_eq_abs] at hn
  exact abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hn

theorem normalUpdate_real_unit (gradient n : ℝ) (hn : ‖n‖ = 1) :
    normalUpdate gradient n = n := by
  rcases real_unit_cases n hn with rfl | rfl
  · simpa only [smul_eq_mul, mul_one] using normalUpdate_smul_self gradient (1 : ℝ) hn
  · simpa only [smul_eq_mul, mul_neg, mul_one, neg_neg] using
      normalUpdate_smul_self (-gradient) (-1 : ℝ) hn

theorem strictMonoOn_intervalRadius_plus :
    StrictMonoOn (fun x : ℝ => x + intervalRadius x) (Icc (-1) 1) := by
  intro x hx y hy hxy
  have hpositive : 0 < (y - x) * (2 - x - y) :=
    mul_pos (sub_pos.mpr hxy) (by linarith [hy.2])
  dsimp [intervalRadius]
  nlinarith

theorem strictMonoOn_intervalRadius_minus :
    StrictMonoOn (fun x : ℝ => x - intervalRadius x) (Icc (-1) 1) := by
  intro x hx y hy hxy
  have hpositive : 0 < (y - x) * (2 + x + y) :=
    mul_pos (sub_pos.mpr hxy) (by linarith [hx.1])
  dsimp [intervalRadius]
  nlinarith

theorem surjOn_intervalRadius_plus :
    SurjOn (fun x : ℝ => x + intervalRadius x) (Icc (-1) 1) (Icc (-1) 1) := by
  have hresult := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
    (continuous_id.add (contDiff_intervalRadius 0).continuous).continuousOn
  simpa only [SurjOn, Pi.add_apply, id_eq, intervalRadius, neg_one_sq, one_pow,
    sub_self, zero_div, add_zero] using hresult

theorem surjOn_intervalRadius_minus :
    SurjOn (fun x : ℝ => x - intervalRadius x) (Icc (-1) 1) (Icc (-1) 1) := by
  have hresult := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
    (continuous_id.sub (contDiff_intervalRadius 0).continuous).continuousOn
  simpa only [intervalRadius, neg_one_sq, one_pow, sub_self, zero_div, sub_zero] using hresult

theorem exponentialMap_intervalRadius :
    ∀ p ∈ (Icc (-1 : ℝ) 1) ×ˢ {n : ℝ | ‖n‖ = 1},
      exponentialMap intervalRadius (fun x => -x) p =
        (p.1 + intervalRadius p.1 * p.2, p.2) := by
  intro p hp
  simp only [exponentialMap, normalUpdate_real_unit _ _ hp.2, smul_eq_mul]

/-- The whole one-dimensional bundle formula is bijective without strict contraction. -/
theorem bijOn_exponentialMap_intervalRadius :
    BijOn (exponentialMap intervalRadius (fun x => -x))
      ((Icc (-1 : ℝ) 1) ×ˢ {n : ℝ | ‖n‖ = 1})
      ((Icc (-1 : ℝ) 1) ×ˢ {n : ℝ | ‖n‖ = 1}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rw [exponentialMap_intervalRadius p hp]
    refine ⟨intervalRadius_ball_subset p.1 hp.1 ?_, hp.2⟩
    rw [Metric.mem_closedBall, Real.dist_eq, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (intervalRadius_bounds p.1 hp.1).1]
    have hnabs : |p.2| = 1 := by simpa only [Real.norm_eq_abs] using hp.2
    rw [hnabs, mul_one]
  · intro p hp q hq heq
    rw [exponentialMap_intervalRadius p hp, exponentialMap_intervalRadius q hq] at heq
    have hnormal := congrArg (fun output : ℝ × ℝ => output.2) heq
    change p.2 = q.2 at hnormal
    apply Prod.ext _ hnormal
    have hposition := congrArg (fun output : ℝ × ℝ => output.1) heq
    change p.1 + intervalRadius p.1 * p.2 = q.1 + intervalRadius q.1 * q.2 at hposition
    rcases real_unit_cases p.2 hp.2 with hpos | hneg
    · have hqpos : q.2 = 1 := hnormal.symm.trans hpos
      simp only [hpos, hqpos, mul_one] at hposition
      exact strictMonoOn_intervalRadius_plus.injOn hp.1 hq.1 hposition
    · have hqneg : q.2 = -1 := hnormal.symm.trans hneg
      simp only [hneg, hqneg, mul_neg_one, ← sub_eq_add_neg] at hposition
      exact strictMonoOn_intervalRadius_minus.injOn hp.1 hq.1 hposition
  · intro p hp
    rcases real_unit_cases p.2 hp.2 with hpos | hneg
    · obtain ⟨x, hx, heq⟩ := surjOn_intervalRadius_plus hp.1
      refine ⟨(x, p.2), ⟨hx, hp.2⟩, ?_⟩
      rw [exponentialMap_intervalRadius (x, p.2) ⟨hx, hp.2⟩]
      apply Prod.ext
      · simpa only [hpos, mul_one] using heq
      · rfl
    · obtain ⟨x, hx, heq⟩ := surjOn_intervalRadius_minus hp.1
      refine ⟨(x, p.2), ⟨hx, hp.2⟩, ?_⟩
      rw [exponentialMap_intervalRadius (x, p.2) ⟨hx, hp.2⟩]
      apply Prod.ext
      · simpa only [hneg, mul_neg_one, ← sub_eq_add_neg] using heq
      · rfl

theorem intervalRadius_not_strict_contraction :
    ¬ ∀ x ∈ Icc (-1 : ℝ) 1, ‖gradient intervalRadius x‖ < 1 := by
  intro h
  have hfalse := h 1 (by norm_num)
  rw [(hasGradientAt_intervalRadius 1).gradient] at hfalse
  norm_num at hfalse

end BoundedUncertainty
