import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Section 3, Definition 3.1 and its local ambient-extension convention.
Functions are represented on the ambient space, but their values outside
the stated domain are unrestricted. No global extension is assumed smooth.
-/

namespace BoundedUncertainty

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def IsRegularClosed (X : Set E) : Prop :=
  closure (interior X) = X

omit [NormedSpace ℝ E] in
theorem IsRegularClosed.isClosed {X : Set E} (hX : IsRegularClosed X) :
    IsClosed X := by
  rw [← hX]
  exact isClosed_closure

/-- A witness for the paper's local extension convention at one point. -/
structure LocalExtensionAt (order : ℕ) (X : Set E) (f : E → F) (x : E) where
  neighborhood : Set E
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : x ∈ neighborhood
  extension : E → F
  contDiffOn_extension : ContDiffOn ℝ order extension neighborhood
  agrees : Set.EqOn extension f (X ∩ neighborhood)

def HasLocalExtensionOn (order : ℕ) (X : Set E) (f : E → F) : Prop :=
  ∀ x ∈ X, Nonempty (LocalExtensionAt order X f x)

theorem HasLocalExtensionOn.continuousOn {order : ℕ} {X : Set E} {f : E → F}
    (h : HasLocalExtensionOn order X f) : ContinuousOn f X := by
  intro x hx
  obtain ⟨extension⟩ := h x hx
  have hcontinuous := extension.contDiffOn_extension.continuousOn.continuousAt
    (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  apply hcontinuous.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)] with y hyX hyU
    exact (extension.agrees ⟨hyX, hyU⟩).symm
  · exact (extension.agrees ⟨hx, extension.mem_neighborhood⟩).symm

/-- Forward local extension together with a nonsingular differential. -/
structure NonsingularLocalExtensionAt (order : ℕ) (X : Set E) (f : E → E) (x : E)
    extends LocalExtensionAt order X f x where
  derivative : E ≃L[ℝ] E
  hasFDerivAt_extension : HasFDerivAt extension (derivative : E →L[ℝ] E) x

/-- A bijection onto its image with the exact local extension convention. -/
structure AmbientDiffeomorphismOn (order : ℕ) (X : Set E) (f : E → E) where
  inverse : E → E
  inverse_mapsTo : Set.MapsTo inverse (f '' X) X
  left_inverse : Set.LeftInvOn inverse f X
  forward_extension : HasLocalExtensionOn order X f
  inverse_extension : HasLocalExtensionOn order (f '' X) inverse
  nonsingular : ∀ x ∈ X, Nonempty (NonsingularLocalExtensionAt order X f x)

theorem AmbientDiffeomorphismOn.injectiveOn {order : ℕ} {X : Set E} {f : E → E}
    (h : AmbientDiffeomorphismOn order X f) : Set.InjOn f X := by
  intro x hx y hy hxy
  calc
    x = h.inverse (f x) := (h.left_inverse hx).symm
    _ = h.inverse (f y) := congrArg h.inverse hxy
    _ = y := h.left_inverse hy

theorem AmbientDiffeomorphismOn.right_inverse {order : ℕ} {X : Set E} {f : E → E}
    (h : AmbientDiffeomorphismOn order X f) : Set.RightInvOn h.inverse f (f '' X) := by
  rintro y ⟨x, hx, rfl⟩
  exact congrArg f (h.left_inverse hx)

def setValuedImage (f : E → E) (ε : E → ℝ) (A : Set E) : Set E :=
  ⋃ x ∈ A, Metric.closedBall (f x) (ε (f x))

def inflation (ε : E → ℝ) (B : Set E) : Set E :=
  ⋃ y ∈ B, Metric.closedBall y (ε y)

omit [NormedSpace ℝ E] in
theorem setValuedImage_eq_inflation (f : E → E) (ε : E → ℝ) (A : Set E) :
    setValuedImage f ε A = inflation ε (f '' A) := by
  ext z
  simp only [setValuedImage, inflation, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hz⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, hz⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, hx, hz⟩

def setValuedIterate (f : E → E) (ε : E → ℝ) : ℕ → Set E → Set E
  | 0, A => A
  | n + 1, A => setValuedImage f ε (setValuedIterate f ε n A)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Definition 3.1. Positivity of the radius itself is deliberately absent. -/
structure SetValuedSystem (r s : ℕ) where
  dimension_at_least_two : 2 ≤ Module.finrank ℝ E
  domain : Set E
  regular_closed : IsRegularClosed domain
  map : E → E
  radius : E → ℝ
  radius_bound : ℝ
  radius_bound_pos : 0 < radius_bound
  radius_order_pos : 1 ≤ r
  map_order_pos : 1 ≤ s
  map_into_domain : Set.MapsTo map domain domain
  diffeomorphism : AmbientDiffeomorphismOn s domain map
  radius_extension : HasLocalExtensionOn r domain radius
  radius_nonneg : ∀ y ∈ domain, 0 ≤ radius y
  radius_le_bound : ∀ y ∈ domain, radius y ≤ radius_bound
  ball_into_domain : ∀ x ∈ domain, Metric.closedBall (map x) (radius (map x)) ⊆ domain

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem SetValuedSystem.image_subset_domain {r s : ℕ} (system : SetValuedSystem (E := E) r s)
    {A : Set E} (hA : A ⊆ system.domain) :
    setValuedImage system.map system.radius A ⊆ system.domain := by
  intro z hz
  obtain ⟨x, hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hxA, hz⟩ := Set.mem_iUnion.mp hz
  exact system.ball_into_domain x (hA hxA) hz

end BoundedUncertainty
