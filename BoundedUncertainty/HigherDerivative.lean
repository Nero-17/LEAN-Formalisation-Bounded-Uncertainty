import BoundedUncertainty.BoundaryMap
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Higher regularity of canonical derivatives and gradients

The manuscript's smoothness convention is local extension to ambient open
neighborhoods. Differentiating those extensions loses one derivative. Equality
of canonical derivatives on a regular closed domain then gives local extensions
for any ambient representative of the derivative field. No global regularity of
the chosen representative and no `UniqueDiffOn` hypothesis on the domain is used.
-/

namespace BoundedUncertainty

section NormedSpaces

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Local ambient extendibility is preserved on lowering the finite regularity order. -/
theorem HasLocalExtensionOn.of_le {order lowerOrder : ℕ} {X : Set E} {f : E → F}
    (h : HasLocalExtensionOn order X f) (horder : lowerOrder ≤ order) :
    HasLocalExtensionOn lowerOrder X f := by
  intro x hx
  obtain ⟨extension⟩ := h x hx
  exact ⟨{
    neighborhood := extension.neighborhood
    isOpen_neighborhood := extension.isOpen_neighborhood
    mem_neighborhood := extension.mem_neighborhood
    extension := extension.extension
    contDiffOn_extension := extension.contDiffOn_extension.of_le (by exact_mod_cast horder)
    agrees := extension.agrees
  }⟩

/-- A continuous linear image of the canonical derivative has local ambient
regularity one order below the original function. The representative may have
arbitrary values outside the original domain. -/
theorem HasLocalExtensionOn.hasLocalExtensionOn_derivative_map
    {order : ℕ} {X : Set E} {f : E → F}
    (h : HasLocalExtensionOn order X f) (hX : IsRegularClosed X) (horder : 1 ≤ order)
    (A : (E →L[ℝ] F) →L[ℝ] G) (D : E → G)
    (hD : ∀ y : X, D y = A (h.ambientDerivative y)) :
    HasLocalExtensionOn (order - 1) X D := by
  intro x hx
  obtain ⟨extension⟩ := h x hx
  have hderivative : ContDiffOn ℝ (order - 1 : ℕ)
      (fderiv ℝ extension.extension) extension.neighborhood :=
    extension.contDiffOn_extension.fderiv_of_isOpen extension.isOpen_neighborhood
      (by exact_mod_cast (Nat.sub_add_cancel horder).le)
  refine ⟨{
    neighborhood := extension.neighborhood
    isOpen_neighborhood := extension.isOpen_neighborhood
    mem_neighborhood := extension.mem_neighborhood
    extension := fun y => A (fderiv ℝ extension.extension y)
    contDiffOn_extension := ContDiffOn.continuousLinearMap_comp A hderivative
    agrees := ?_
  }⟩
  intro y hy
  calc
    A (fderiv ℝ extension.extension y) = A (h.ambientDerivative ⟨y, hy.1⟩) :=
      congrArg A (h.ambientDerivative_eq_extension hX horder horder extension
        ⟨y, hy.1⟩ hy.2).symm
    _ = D y := (hD ⟨y, hy.1⟩).symm

/-- Any ambient representative agreeing with the canonical differential on the
domain has local ambient regularity one order below the original function. -/
theorem HasLocalExtensionOn.hasLocalExtensionOn_derivative_rep
    {order : ℕ} {X : Set E} {f : E → F}
    (h : HasLocalExtensionOn order X f) (hX : IsRegularClosed X) (horder : 1 ≤ order)
    (D : E → E →L[ℝ] F) (hD : ∀ y : X, D y = h.ambientDerivative y) :
    HasLocalExtensionOn (order - 1) X D :=
  h.hasLocalExtensionOn_derivative_map hX horder
    (ContinuousLinearMap.id ℝ (E →L[ℝ] F)) D hD

end NormedSpaces

section System

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r s : ℕ}

/-- A total representative of the canonical map differential. Its zero values
outside the domain carry no continuity or differentiability assertion. -/
noncomputable def SetValuedSystem.mapDerivativeOnAmbient
    (system : SetValuedSystem (E := E) r s) (x : E) : E →L[ℝ] E := by
  classical
  exact if hx : x ∈ system.domain then
    system.diffeomorphism.forward_extension.ambientDerivative ⟨x, hx⟩ else 0

@[simp] theorem SetValuedSystem.mapDerivativeOnAmbient_apply
    (system : SetValuedSystem (E := E) r s) (x : system.domain) :
    system.mapDerivativeOnAmbient x =
      system.diffeomorphism.forward_extension.ambientDerivative x := by
  simp [SetValuedSystem.mapDerivativeOnAmbient, x.property]

/-- The ambient representative is the true differential represented by the
previously constructed linear equivalence at every source point. -/
theorem SetValuedSystem.mapDerivativeOnAmbient_eq_derivativeEquiv
    (system : SetValuedSystem (E := E) r s) (x : system.domain) :
    system.mapDerivativeOnAmbient x = (system.derivativeEquiv x : E →L[ℝ] E) := by
  rw [system.mapDerivativeOnAmbient_apply, system.derivativeEquiv_eq_ambientDerivative]

/-- The canonical map differential admits local `C^(s-1)` ambient extensions. -/
theorem SetValuedSystem.hasLocalExtensionOn_mapDerivativeOnAmbient
    (system : SetValuedSystem (E := E) r s) :
    HasLocalExtensionOn (s - 1) system.domain system.mapDerivativeOnAmbient :=
  system.diffeomorphism.forward_extension.hasLocalExtensionOn_derivative_rep
    system.regular_closed system.map_order_pos system.mapDerivativeOnAmbient
    system.mapDerivativeOnAmbient_apply

variable [CompleteSpace E]

/-- The genuine radius gradient admits local `C^(r-1)` ambient extensions,
including at domain boundary points. The zero representative itself need not
be smooth outside the domain. -/
theorem SetValuedSystem.hasLocalExtensionOn_radiusGradientOnAmbient
    (system : SetValuedSystem (E := E) r s) :
    HasLocalExtensionOn (r - 1) system.domain system.radiusGradientOnAmbient := by
  apply system.radius_extension.hasLocalExtensionOn_derivative_map
    system.regular_closed system.radius_order_pos
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  intro y
  exact system.radiusGradientOnAmbient_apply y

end System

end BoundedUncertainty
