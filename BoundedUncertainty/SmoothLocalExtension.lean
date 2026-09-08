import BoundedUncertainty.HigherDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# A single smooth local extension

The witness below is C-infinity on one fixed open neighborhood. It is not a
family of unrelated finite-order witnesses, and it is stronger than merely
asserting `ContDiffAt infinity` at the marked point.
-/

namespace BoundedUncertainty

open Set Filter Topology
open scoped ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- One fixed open-neighborhood extension which is smooth on that entire neighborhood. -/
structure SmoothLocalExtensionAt (X : Set E) (f : E → F) (x : E) where
  neighborhood : Set E
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : x ∈ neighborhood
  extension : E → F
  contDiffOn_extension : ContDiffOn ℝ ∞ extension neighborhood
  agrees : EqOn extension f (X ∩ neighborhood)

def HasSmoothLocalExtensionOn (X : Set E) (f : E → F) : Prop :=
  ∀ x ∈ X, Nonempty (SmoothLocalExtensionAt X f x)

/-- The same fixed smooth witness supplies every finite regularity order. -/
def SmoothLocalExtensionAt.toLocalExtensionAt {X : Set E} {f : E → F} {x : E}
    (extension : SmoothLocalExtensionAt X f x) (order : ℕ) : LocalExtensionAt order X f x where
  neighborhood := extension.neighborhood
  isOpen_neighborhood := extension.isOpen_neighborhood
  mem_neighborhood := extension.mem_neighborhood
  extension := extension.extension
  contDiffOn_extension := extension.contDiffOn_extension.of_le
    (WithTop.coe_le_coe.mpr (le_top : (order : ℕ∞) ≤ ⊤))
  agrees := extension.agrees

theorem HasSmoothLocalExtensionOn.toHasLocalExtensionOn {X : Set E} {f : E → F}
    (h : HasSmoothLocalExtensionOn X f) (order : ℕ) : HasLocalExtensionOn order X f := by
  intro x hx
  obtain ⟨extension⟩ := h x hx
  exact ⟨extension.toLocalExtensionAt order⟩

theorem HasSmoothLocalExtensionOn.continuousOn {X : Set E} {f : E → F}
    (h : HasSmoothLocalExtensionOn X f) : ContinuousOn f X :=
  (h.toHasLocalExtensionOn 1).continuousOn

theorem HasSmoothLocalExtensionOn.mono_domain {X Y : Set E} {f : E → F}
    (h : HasSmoothLocalExtensionOn X f) (hYX : Y ⊆ X) : HasSmoothLocalExtensionOn Y f := by
  intro x hx
  obtain ⟨extension⟩ := h x (hYX hx)
  exact ⟨{
    neighborhood := extension.neighborhood
    isOpen_neighborhood := extension.isOpen_neighborhood
    mem_neighborhood := extension.mem_neighborhood
    extension := extension.extension
    contDiffOn_extension := extension.contDiffOn_extension
    agrees := fun y hy => extension.agrees ⟨hYX hy.1, hy.2⟩
  }⟩

theorem HasSmoothLocalExtensionOn.congr {X : Set E} {f g : E → F}
    (h : HasSmoothLocalExtensionOn X f) (heq : EqOn f g X) : HasSmoothLocalExtensionOn X g := by
  intro x hx
  obtain ⟨extension⟩ := h x hx
  exact ⟨{
    neighborhood := extension.neighborhood
    isOpen_neighborhood := extension.isOpen_neighborhood
    mem_neighborhood := extension.mem_neighborhood
    extension := extension.extension
    contDiffOn_extension := extension.contDiffOn_extension
    agrees := fun y hy => (extension.agrees hy).trans (heq hy.1)
  }⟩

/-- A fixed smooth neighborhood together with eventual agreement supplies a
smooth local extension after shrinking the neighborhood once. -/
theorem hasSmoothLocalExtensionOn_of_locally_contDiffOn {X : Set E} {f : E → F}
    (h : ∀ x ∈ X, ∃ extension : E → F, ∃ U : Set E,
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ extension U ∧
        ∀ᶠ y in 𝓝 x, y ∈ X → extension y = f y) :
    HasSmoothLocalExtensionOn X f := by
  intro x hx
  obtain ⟨extension, U, hUopen, hxU, hUsmooth, hagrees⟩ := h x hx
  obtain ⟨V, hVsubset, hVopen, hxV⟩ := mem_nhds_iff.mp
    (inter_mem (hUopen.mem_nhds hxU) hagrees)
  exact ⟨{
    neighborhood := V
    isOpen_neighborhood := hVopen
    mem_neighborhood := hxV
    extension := extension
    contDiffOn_extension := hUsmooth.mono (fun y hy => (hVsubset hy).1)
    agrees := fun y hy => (hVsubset hy.2).2 hy.1
  }⟩

/-- Composition preserves one fixed smooth neighborhood for each source point. -/
theorem HasSmoothLocalExtensionOn.comp {X : Set E} {Y : Set F}
    {f : E → F} {g : F → G}
    (hg : HasSmoothLocalExtensionOn Y g) (hf : HasSmoothLocalExtensionOn X f)
    (himage : MapsTo f X Y) : HasSmoothLocalExtensionOn X (g ∘ f) := by
  intro x hx
  obtain ⟨innerExtension⟩ := hf x hx
  obtain ⟨outerExtension⟩ := hg (f x) (himage hx)
  have hvalue : innerExtension.extension x = f x :=
    innerExtension.agrees ⟨hx, innerExtension.mem_neighborhood⟩
  have htarget : outerExtension.neighborhood ∈ 𝓝 (innerExtension.extension x) := by
    rw [hvalue]
    exact outerExtension.isOpen_neighborhood.mem_nhds outerExtension.mem_neighborhood
  have hinnerContinuous : ContinuousAt innerExtension.extension x :=
    innerExtension.contDiffOn_extension.continuousOn.continuousAt
      (innerExtension.isOpen_neighborhood.mem_nhds innerExtension.mem_neighborhood)
  obtain ⟨U, hUsubset, hUopen, hxU⟩ := mem_nhds_iff.mp
    (inter_mem (innerExtension.isOpen_neighborhood.mem_nhds innerExtension.mem_neighborhood)
      (hinnerContinuous.preimage_mem_nhds htarget))
  refine ⟨{
    neighborhood := U
    isOpen_neighborhood := hUopen
    mem_neighborhood := hxU
    extension := outerExtension.extension ∘ innerExtension.extension
    contDiffOn_extension := outerExtension.contDiffOn_extension.comp
      (innerExtension.contDiffOn_extension.mono (fun y hy => (hUsubset hy).1))
      (fun y hy => (hUsubset hy).2)
    agrees := ?_
  }⟩
  intro y hy
  have hinnerValue := innerExtension.agrees ⟨hy.1, (hUsubset hy.2).1⟩
  change outerExtension.extension (innerExtension.extension y) = g (f y)
  rw [hinnerValue]
  exact outerExtension.agrees ⟨himage hy.1, hinnerValue ▸ (hUsubset hy.2).2⟩

/-- Differentiating a fixed smooth extension keeps that same open neighborhood. -/
theorem HasSmoothLocalExtensionOn.derivative_map
    {order : ℕ} {X : Set E} {f : E → F}
    (hsmooth : HasSmoothLocalExtensionOn X f) (h : HasLocalExtensionOn order X f)
    (hX : IsRegularClosed X) (horder : 1 ≤ order)
    (A : (E →L[ℝ] F) →L[ℝ] G) (D : E → G)
    (hD : ∀ y : X, D y = A (h.ambientDerivative y)) :
    HasSmoothLocalExtensionOn X D := by
  intro x hx
  obtain ⟨extension⟩ := hsmooth x hx
  refine ⟨{
    neighborhood := extension.neighborhood
    isOpen_neighborhood := extension.isOpen_neighborhood
    mem_neighborhood := extension.mem_neighborhood
    extension := fun y => A (fderiv ℝ extension.extension y)
    contDiffOn_extension := ContDiffOn.continuousLinearMap_comp A
      (extension.contDiffOn_extension.fderiv_of_isOpen extension.isOpen_neighborhood (by simp))
    agrees := ?_
  }⟩
  intro y hy
  calc
    A (fderiv ℝ extension.extension y) = A (h.ambientDerivative ⟨y, hy.1⟩) :=
      congrArg A (h.ambientDerivative_eq_extension hX horder (by decide : 1 ≤ 1)
        (extension.toLocalExtensionAt 1) ⟨y, hy.1⟩ hy.2).symm
    _ = D y := (hD ⟨y, hy.1⟩).symm

end BoundedUncertainty
