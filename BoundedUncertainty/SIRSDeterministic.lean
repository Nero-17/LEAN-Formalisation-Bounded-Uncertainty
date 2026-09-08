import BoundedUncertainty.SIRSAlgebra
import BoundedUncertainty.SIRSGeometry
import BoundedUncertainty.CompactSmoothInverse
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The exact deterministic SIRS map in Example 3.13: actual differential,
Jacobian determinant, and injectivity on the simplex. -/

namespace BoundedUncertainty

open Set
open scoped ContDiff

noncomputable def sirsJacobian (p : EuclideanSpace ℝ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![19 / 20 - (3 / 10) * p 1, -1 / 20 - (3 / 10) * p 0;
    (3 / 10) * p 1, 9 / 10 + (3 / 10) * p 0]

noncomputable def sirsDerivative (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Matrix.toLpLin 2 2 (sirsJacobian p)).toContinuousLinearMap

theorem sirsDerivative_apply (p v : EuclideanSpace ℝ (Fin 2)) :
    sirsDerivative p v =
      !₂[(19 / 20 - (3 / 10) * p 1) * v 0 + (-1 / 20 - (3 / 10) * p 0) * v 1,
        ((3 / 10) * p 1) * v 0 + (9 / 10 + (3 / 10) * p 0) * v 1] := by
  ext i
  fin_cases i <;> simp [sirsDerivative, sirsJacobian, Matrix.toLpLin_apply,
    Matrix.vecHead, Matrix.vecTail]

theorem hasFDerivAt_sirsMap (p : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (sirsMap (1 / 10) 1 3) (sirsDerivative p) p := by
  have hfirst := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).hasFDerivAt (x := p)
  have hsecond := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).hasFDerivAt (x := p)
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  · convert ((hfirst.mul ((hasFDerivAt_const (1 : ℝ) p).sub
      (hsecond.const_mul (3 / 10)))).add
      ((((hasFDerivAt_const (1 : ℝ) p).sub hfirst).sub hsecond).const_mul (1 / 20))).hasFDerivWithinAt using 1
    · ext q
      exact sirsMap_first_coordinate q
    · ext v
      simp [sirsDerivative_apply]
      ring
  · convert (hsecond.mul ((hasFDerivAt_const (9 / 10 : ℝ) p).add
      (hfirst.const_mul (3 / 10)))).hasFDerivWithinAt using 1
    · ext q
      exact sirsMap_second_coordinate q
    · ext v
      simp [sirsDerivative_apply]
      ring

theorem fderiv_sirsMap (p : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (sirsMap (1 / 10) 1 3) p = sirsDerivative p :=
  (hasFDerivAt_sirsMap p).fderiv

theorem det_sirsJacobian (p : EuclideanSpace ℝ (Fin 2)) :
    (sirsJacobian p).det = 171 / 200 + (57 / 200) * p 0 - (51 / 200) * p 1 := by
  rw [Matrix.det_fin_two]
  dsimp [sirsJacobian]
  ring

theorem det_sirsJacobian_lower_bound (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ sirsSimplex) : (3 / 5 : ℝ) ≤ (sirsJacobian p).det := by
  rw [det_sirsJacobian]
  rcases hp with ⟨hS, hI, hsum⟩
  linarith

theorem sirsMap_injectiveOn : Set.InjOn (sirsMap (1 / 10) 1 3) sirsSimplex := by
  intro p hp q hq heq
  have hfirst := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
  have hsecond := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) heq
  dsimp only at hfirst hsecond
  rw [sirsMap_first_coordinate, sirsMap_first_coordinate] at hfirst
  rw [sirsMap_second_coordinate, sirsMap_second_coordinate] at hsecond
  have hlinear : 19 * (p 0 - q 0) + 17 * (p 1 - q 1) = 0 := by
    nlinarith
  have hweighted := congrArg (fun t : ℝ => q 1 * t) hlinear
  have hproduct : (171 + 57 * p 0 - 51 * q 1) * (p 1 - q 1) = 0 := by
    dsimp at hweighted
    nlinarith
  have hpositive : 0 < 171 + 57 * p 0 - 51 * q 1 := by
    nlinarith [hp.1, hq.1, hq.2.2]
  have hsecondEq : p 1 = q 1 := sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hpositive))
  have hfirstEq : p 0 = q 0 := by linarith
  ext i
  fin_cases i
  · exact hfirstEq
  · exact hsecondEq

theorem sirsDerivative_injective_of_positive (p : EuclideanSpace ℝ (Fin 2))
    (hpositive : 0 < 171 + 57 * p 0 - 51 * p 1) :
    Function.Injective (sirsDerivative p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change sirsDerivative p v = 0 at hv
  have hfirst := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hv
  have hsecond := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hv
  simp only [sirsDerivative_apply] at hfirst hsecond
  change (19 / 20 - (3 / 10) * p 1) * v 0 +
    (-1 / 20 - (3 / 10) * p 0) * v 1 = 0 at hfirst
  change ((3 / 10) * p 1) * v 0 + (9 / 10 + (3 / 10) * p 0) * v 1 = 0 at hsecond
  have hlinear : 19 * v 0 + 17 * v 1 = 0 := by nlinarith
  have hweighted := congrArg (fun t : ℝ => p 1 * t) hlinear
  have hproduct : (171 + 57 * p 0 - 51 * p 1) * v 1 = 0 := by
    dsimp at hweighted
    nlinarith
  have hsecondZero : v 1 = 0 := (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hpositive)
  have hfirstZero : v 0 = 0 := by linarith
  ext i
  fin_cases i
  · exact hfirstZero
  · exact hsecondZero

theorem sirsDerivative_injective (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    Function.Injective (sirsDerivative p) :=
  sirsDerivative_injective_of_positive p (by nlinarith [hp.1, hp.2.2])

noncomputable def sirsDerivativeEquiv (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.ofInjectiveEndo (sirsDerivative p).toLinearMap (sirsDerivative_injective p hp)).toContinuousLinearEquiv

theorem hasFDerivAt_sirsMap_equiv (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ sirsSimplex) :
    HasFDerivAt (sirsMap (1 / 10) 1 3)
      (sirsDerivativeEquiv p hp : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) p :=
  hasFDerivAt_sirsMap p

/-- A proved open nonsingular neighborhood of the entire simplex. -/
theorem sirsMap_nonsingular_on_open :
    ∀ p ∈ {p : EuclideanSpace ℝ (Fin 2) | 0 < 171 + 57 * p 0 - 51 * p 1},
      ∃ derivative : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2),
        HasFDerivAt (sirsMap (1 / 10) 1 3)
          (derivative : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) p := by
  intro p hp
  exact ⟨(LinearEquiv.ofInjectiveEndo (sirsDerivative p).toLinearMap
    (sirsDerivative_injective_of_positive p hp)).toContinuousLinearEquiv,
    hasFDerivAt_sirsMap p⟩

theorem hasSmoothLocalExtensionOn_sirsMap_inverse :
    HasSmoothLocalExtensionOn (sirsMap (1 / 10) 1 3 '' sirsSimplex)
      (Function.invFunOn (sirsMap (1 / 10) 1 3) sirsSimplex) := by
  apply hasSmoothLocalExtensionOn_invFunOn_of_compact
    (sirsMap (1 / 10) 1 3) sirsSimplex isCompact_sirsSimplex
    (contDiff_sirsMap (1 / 10) 1 3 ∞) sirsMap_injectiveOn
    {p : EuclideanSpace ℝ (Fin 2) | 0 < 171 + 57 * p 0 - 51 * p 1}
  · exact isOpen_lt continuous_const (by fun_prop)
  · intro p hp
    dsimp only [Set.mem_setOf_eq]
    nlinarith [hp.1, hp.2.2]
  · exact sirsMap_nonsingular_on_open

/-- The actual deterministic map satisfies the paper's diffeomorphism convention at every order. -/
noncomputable def sirsAmbientDiffeomorphism (order : ℕ) :
    AmbientDiffeomorphismOn order sirsSimplex (sirsMap (1 / 10) 1 3) :=
  ambientDiffeomorphismOn_of_compact_smooth
    (sirsMap (1 / 10) 1 3) sirsSimplex isCompact_sirsSimplex
    (contDiff_sirsMap (1 / 10) 1 3 ∞) sirsMap_injectiveOn
    {p : EuclideanSpace ℝ (Fin 2) | 0 < 171 + 57 * p 0 - 51 * p 1}
    (isOpen_lt continuous_const (by fun_prop))
    (fun p hp => by dsimp only [Set.mem_setOf_eq]; nlinarith [hp.1, hp.2.2])
    sirsMap_nonsingular_on_open order

theorem sirsAmbientDiffeomorphism_inverse (order : ℕ) :
    (sirsAmbientDiffeomorphism order).inverse =
      Function.invFunOn (sirsMap (1 / 10) 1 3) sirsSimplex := rfl

/-- In particular the inverse used at any finite order is the same inverse with a fixed smooth witness. -/
theorem sirsAmbientDiffeomorphism_inverse_smooth (order : ℕ) :
    HasSmoothLocalExtensionOn (sirsMap (1 / 10) 1 3 '' sirsSimplex)
      (sirsAmbientDiffeomorphism order).inverse :=
  hasSmoothLocalExtensionOn_sirsMap_inverse

end BoundedUncertainty
