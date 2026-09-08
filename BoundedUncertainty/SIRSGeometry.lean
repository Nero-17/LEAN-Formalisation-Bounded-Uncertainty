import BoundedUncertainty.SIRSAlgebra
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The closed triangular state space in Example 3.13. -/
namespace BoundedUncertainty
open Set

theorem isClosed_sirsSimplex : IsClosed sirsSimplex := by
  change IsClosed ({p : EuclideanSpace ℝ (Fin 2) | 0 ≤ p 0} ∩
    ({p | 0 ≤ p 1} ∩ {p | p 0 + p 1 ≤ 1}))
  exact (isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const))

theorem convex_sirsSimplex : Convex ℝ sirsSimplex := by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a * p 0 + b * q 0 ∧ 0 ≤ a * p 1 + b * q 1 ∧
    a * p 0 + b * q 0 + (a * p 1 + b * q 1) ≤ 1
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
    add_nonneg (mul_nonneg ha hp.2.1) (mul_nonneg hb hq.2.1), ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hp.2.2 ha, mul_le_mul_of_nonneg_left hq.2.2 hb]

theorem isCompact_sirsSimplex : IsCompact sirsSimplex := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_sirsSimplex, isBounded_iff_forall_norm_le.mpr ⟨2, ?_⟩⟩
  intro p hp
  have hsq : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, sq_abs]
  have hfirst : p 0 ≤ 1 := by linarith [hp.2.1, hp.2.2]
  have hsecond : p 1 ≤ 1 := by linarith [hp.1, hp.2.2]
  nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hfirst),
    mul_nonneg hp.2.1 (sub_nonneg.mpr hsecond), norm_nonneg p]

theorem pos_of_nonneg_of_mem_interior_of_hasFDerivAt_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Set E) (f : E → ℝ) (p : E) (derivative : E →L[ℝ] ℝ)
    (hnonneg : ∀ q ∈ B, 0 ≤ f q) (hp : p ∈ interior B)
    (hderivative : HasFDerivAt f derivative p) (hne : derivative ≠ 0) : 0 < f p := by
  have hvalue := hnonneg p (interior_subset hp)
  apply lt_of_le_of_ne hvalue
  intro heq
  apply hne
  apply IsLocalMin.hasFDerivAt_eq_zero (f := f) (a := p) _ hderivative
  show ∀ᶠ q in nhds p, f p ≤ f q
  filter_upwards [isOpen_interior.mem_nhds hp] with q hq
  simpa only [← heq] using hnonneg q (interior_subset hq)

theorem mem_interior_sirsSimplex (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ interior sirsSimplex ↔ 0 < p 0 ∧ 0 < p 1 ∧ p 0 + p 1 < 1 := by
  constructor
  · intro hp
    have hfirst := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := p)
    have hsecond := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := p)
    have hfirstNe : PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 ≠ 0 := by
      intro heq
      have := congrArg (fun T : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => T !₂[1, 0]) heq
      norm_num at this
    have hsecondNe : PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 ≠ 0 := by
      intro heq
      have := congrArg (fun T : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => T !₂[0, 1]) heq
      norm_num at this
    have hsumNe : 0 - PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0 -
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1 ≠ 0 := by
      intro heq
      have := congrArg (fun T : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ => T !₂[1, 0]) heq
      norm_num at this
    refine ⟨pos_of_nonneg_of_mem_interior_of_hasFDerivAt_ne_zero sirsSimplex _ p _
      (fun _ hq => hq.1) hp hfirst hfirstNe,
      pos_of_nonneg_of_mem_interior_of_hasFDerivAt_ne_zero sirsSimplex _ p _
      (fun _ hq => hq.2.1) hp hsecond hsecondNe, ?_⟩
    have hpos := pos_of_nonneg_of_mem_interior_of_hasFDerivAt_ne_zero sirsSimplex
      (fun q => 1 - q 0 - q 1) p _ (fun _ hq => by linarith [hq.2.2]) hp
      (((hasFDerivAt_const (1 : ℝ) p).sub hfirst).sub hsecond) hsumNe
    linarith
  · intro hp
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin 2) |
        0 < q 0 ∧ 0 < q 1 ∧ q 0 + q 1 < 1} := by
      change IsOpen ({q : EuclideanSpace ℝ (Fin 2) | 0 < q 0} ∩
        ({q | 0 < q 1} ∩ {q | q 0 + q 1 < 1}))
      exact (isOpen_lt continuous_const (by fun_prop)).inter
        ((isOpen_lt continuous_const (by fun_prop)).inter
          (isOpen_lt (by fun_prop) continuous_const))
    apply (interior_maximal _ hopen) hp
    intro q hq
    exact ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩

theorem isRegularClosed_sirsSimplex : IsRegularClosed sirsSimplex := by
  rw [IsRegularClosed, convex_sirsSimplex.closure_interior_eq_closure_of_nonempty_interior,
    isClosed_sirsSimplex.closure_eq]
  exact ⟨!₂[(1 : ℝ) / 3, 1 / 3], (mem_interior_sirsSimplex _).mpr (by norm_num)⟩

theorem mem_frontier_sirsSimplex (p : EuclideanSpace ℝ (Fin 2)) :
    p ∈ frontier sirsSimplex ↔ p ∈ sirsSimplex ∧
      (p 0 = 0 ∨ p 1 = 0 ∨ p 0 + p 1 = 1) := by
  rw [isClosed_sirsSimplex.frontier_eq, mem_diff, mem_interior_sirsSimplex]
  constructor
  · rintro ⟨hp, hnot⟩
    refine ⟨hp, ?_⟩
    by_contra hnone
    push_neg at hnone
    exact hnot ⟨lt_of_le_of_ne hp.1 (Ne.symm hnone.1),
      lt_of_le_of_ne hp.2.1 (Ne.symm hnone.2.1), lt_of_le_of_ne hp.2.2 hnone.2.2⟩
  · rintro ⟨hp, hzero⟩
    refine ⟨hp, ?_⟩
    rintro ⟨hfirst, hsecond, hsum⟩
    rcases hzero with hzero | hzero | hzero <;> linarith

theorem sirsRadius_eq_zero_iff_mem_frontier (κ : ℝ) (hκ : 0 < κ)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    sirsRadius κ p = 0 ↔ p ∈ frontier sirsSimplex := by
  rw [mem_frontier_sirsSimplex, and_iff_right hp]
  have hdiv : κ / 10 ≠ 0 := ne_of_gt (div_pos hκ (by norm_num))
  simp only [sirsRadius, mul_eq_zero, hdiv, false_or]
  constructor
  · rintro ((hfirst | hsecond) | hsum)
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hsecond)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (hfirst | hsecond | hsum)
    · exact Or.inl (Or.inl hfirst)
    · exact Or.inl (Or.inr hsecond)
    · exact Or.inr (by linarith)

end BoundedUncertainty
