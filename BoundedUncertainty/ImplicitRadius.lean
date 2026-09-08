import BoundedUncertainty.HigherExponential
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The scalar implicit equation for recovering an exponential centre

The radius is recovered from `q - ε (z - q • u) = 0`.  The partial derivative
in `q` is `1 + Dε(y) u`.  This module constructs a smooth local solution and
records local uniqueness; it makes no global inverse assertion.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The scalar equation whose zero set recovers the preimage centre. -/
def radiusImplicitEquation (ε : E → ℝ) (p : (E × E) × ℝ) : ℝ :=
  p.2 - ε (p.1.1 - p.2 • p.1.2)

omit [CompleteSpace E] in
/-- Pointwise contraction makes the partial derivative in the scalar variable positive. -/
theorem radiusImplicitEquation_partial_pos (gradient u : E)
    (hgradient : ‖gradient‖ < 1) (hu : ‖u‖ = 1) :
    0 < 1 + inner ℝ gradient u := by
  have hinner := abs_real_inner_le_norm gradient u
  rw [hu, mul_one] at hinner
  have hlower := neg_abs_le (inner ℝ gradient u)
  linarith

/-- A smooth radius has a smooth scalar implicit solution near the image of
any centre for which the scalar partial derivative is nonzero.  The final
clause gives uniqueness among all sufficiently nearby solutions. -/
theorem exists_contDiffAt_radiusImplicitSolution {order : ℕ}
    (ε : E → ℝ) (y u : E) (Dε : E →L[ℝ] ℝ)
    (horder : 1 ≤ order) (hε : ContDiffAt ℝ order ε y)
    (hderivative : HasFDerivAt ε Dε y) (hnonzero : 1 + Dε u ≠ 0) :
    ∃ solution : E × E → ℝ,
      ContDiffAt ℝ order solution (y + ε y • u, u) ∧
      solution (y + ε y • u, u) = ε y ∧
      (∀ᶠ p in 𝓝 (y + ε y • u, u),
        radiusImplicitEquation ε (p, solution p) = 0) ∧
      (∀ᶠ p in 𝓝 ((y + ε y • u, u), ε y),
        radiusImplicitEquation ε p = 0 → solution p.1 = p.2) := by
  have hcentre : y + ε y • u - ε y • u = y := add_sub_cancel_right y _
  have hcontdiff : ContDiffAt ℝ order (radiusImplicitEquation ε)
      ((y + ε y • u, u), ε y) := by
    apply contDiffAt_snd.sub
    have hε' : ContDiffAt ℝ order ε (y + ε y • u - ε y • u) := hcentre.symm ▸ hε
    exact hε'.comp ((y + ε y • u, u), ε y)
      (f := fun p : (E × E) × ℝ => p.1.1 - p.2 • p.1.2)
      ((contDiffAt_fst.fst).sub (contDiffAt_snd.smul contDiffAt_fst.snd))
  have hdifferentiable := hcontdiff.differentiableAt
    (by exact_mod_cast (Nat.ne_of_gt horder))
  have hslice : HasFDerivAt (fun q : ℝ => ((y + ε y • u, u), q))
      (ContinuousLinearMap.inr ℝ (E × E) ℝ) (ε y) := by
    simpa using (hasFDerivAt_const (y + ε y • u, u) (ε y)).prodMk
      (hasFDerivAt_id (ε y))
  have hpartial := hdifferentiable.hasFDerivAt.comp (ε y) hslice
  have hline : HasDerivAt (fun q : ℝ => y + ε y • u - q • u) (-u) (ε y) := by
    simpa using (hasDerivAt_const (ε y) (y + ε y • u)).sub
      ((hasDerivAt_id (ε y)).smul_const u)
  have hscalar : HasDerivAt (fun q : ℝ =>
      radiusImplicitEquation ε ((y + ε y • u, u), q)) (1 + Dε u) (ε y) := by
    simpa [radiusImplicitEquation, Function.comp_def, map_neg, sub_neg_eq_add] using
      (hasDerivAt_id (ε y)).sub
        (hderivative.comp_hasDerivAt_of_eq (ε y) hline hcentre.symm)
  have himplicit : IsContDiffImplicitAt (order : WithTop ℕ∞)
      (radiusImplicitEquation ε)
      (fderiv ℝ (radiusImplicitEquation ε) ((y + ε y • u, u), ε y))
      ((y + ε y • u, u), ε y) := {
    hasFDerivAt := hdifferentiable.hasFDerivAt
    contDiffAt := hcontdiff
    bijective := by
      rw [hpartial.unique hscalar.hasFDerivAt]
      constructor
      · intro a b hab
        have heq : a * (1 + Dε u) = b * (1 + Dε u) := hab
        exact mul_right_cancel₀ hnonzero heq
      · intro b
        refine ⟨b / (1 + Dε u), ?_⟩
        change b / (1 + Dε u) * (1 + Dε u) = b
        exact div_mul_cancel₀ b hnonzero
    ne_zero := by exact_mod_cast (Nat.ne_of_gt horder)
  }
  have hequation : radiusImplicitEquation ε ((y + ε y • u, u), ε y) = 0 := by
    simp only [radiusImplicitEquation, hcentre, sub_self]
  refine ⟨himplicit.implicitFunction, himplicit.contDiffAt_implicitFunction, ?_, ?_, ?_⟩
  · exact himplicit.eventually_implicitFunction_apply_eq.self_of_nhds rfl
  · simpa only [hequation] using himplicit.apply_implicitFunction
  · simpa only [hequation] using himplicit.eventually_implicitFunction_apply_eq

end BoundedUncertainty
