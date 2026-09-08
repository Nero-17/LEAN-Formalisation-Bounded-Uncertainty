import BoundedUncertainty.ContributorFormula
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! Explicit source interfaces for Notation 3.3 and globally smooth examples. -/

namespace BoundedUncertainty

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasLocalExtensionOn_of_contDiff (order : ℕ) (X : Set E) (f : E → F)
    (h : ContDiff ℝ order f) : HasLocalExtensionOn order X f := by
  intro x hx
  exact ⟨{
    neighborhood := univ
    isOpen_neighborhood := isOpen_univ
    mem_neighborhood := mem_univ x
    extension := f
    contDiffOn_extension := h.contDiffOn
    agrees := fun _ _ => rfl
  }⟩

def ambientDiffeomorphismOn_id (order : ℕ) (X : Set E) :
    AmbientDiffeomorphismOn order X (id : E → E) where
  inverse := id
  inverse_mapsTo := by simpa only [image_id] using (mapsTo_id X)
  left_inverse := fun _ _ => rfl
  forward_extension := hasLocalExtensionOn_of_contDiff order X id contDiff_id
  inverse_extension := hasLocalExtensionOn_of_contDiff order (id '' X) id contDiff_id
  nonsingular x _ := ⟨{
    neighborhood := univ
    isOpen_neighborhood := isOpen_univ
    mem_neighborhood := mem_univ x
    extension := id
    contDiffOn_extension := contDiffOn_id
    agrees := fun _ _ => rfl
    derivative := ContinuousLinearEquiv.refl ℝ E
    hasFDerivAt_extension := hasFDerivAt_id x
  }⟩

/-- The paper's contributing pair is defined with the actual frontier of the constituent ball. -/
def IsContributingPair (radius : E → ℝ) (B : Set E) (y z : E) : Prop :=
  y ∈ B ∧ z ∈ frontier (inflation radius B) ∧
    z ∈ frontier (Metric.closedBall y (radius y))

/-- Uniqueness is specifically among contributors on the source frontier. -/
def IsUniqueContributingPair (radius : E → ℝ) (B : Set E) (y z : E) : Prop :=
  IsContributingPair radius B y z ∧
    ∀ other ∈ frontier B, IsContributingPair radius B other z → other = y

theorem isContributingPair_iff_dist [Nontrivial E] (radius : E → ℝ) (B : Set E) (y z : E) :
    IsContributingPair radius B y z ↔
      y ∈ B ∧ z ∈ frontier (inflation radius B) ∧ dist z y = radius y := by
  simp only [IsContributingPair, frontier_closedBall', Metric.mem_sphere]

end BoundedUncertainty
