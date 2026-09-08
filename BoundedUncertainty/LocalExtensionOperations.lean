import BoundedUncertainty.HigherDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Local extension operations, with finite regularity and arbitrary source sets. -/

namespace BoundedUncertainty

open Set Filter Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A locally smooth representative that agrees near the point on the source
set supplies an open-neighborhood extension in the manuscript's convention. -/
theorem hasLocalExtensionOn_of_locally_contDiffAt {order : ℕ} {X : Set E} {f : E → F}
    (h : ∀ x ∈ X, ∃ extension : E → F,
      ContDiffAt ℝ order extension x ∧
        ∀ᶠ y in 𝓝 x, y ∈ X → extension y = f y) :
    HasLocalExtensionOn order X f := by
  intro x hx
  obtain ⟨extension, hcontdiff, hagrees⟩ := h x hx
  obtain ⟨U, hUnhds, hUcontdiff⟩ := hcontdiff.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVsubset, hVopen, hxV⟩ := mem_nhds_iff.mp (inter_mem hUnhds hagrees)
  exact ⟨{
    neighborhood := V
    isOpen_neighborhood := hVopen
    mem_neighborhood := hxV
    extension := extension
    contDiffOn_extension := hUcontdiff.mono (fun _ hy => (hVsubset hy).1)
    agrees := fun _ hy => (hVsubset hy.2).2 hy.1
  }⟩

/-- Local ambient extensions compose whenever the inner map takes the source
set into the set on which the outer map has local extensions. -/
theorem HasLocalExtensionOn.comp {order : ℕ} {X : Set E} {Y : Set F}
    {f : E → F} {g : F → G}
    (hg : HasLocalExtensionOn order Y g) (hf : HasLocalExtensionOn order X f)
    (himage : Set.MapsTo f X Y) : HasLocalExtensionOn order X (g ∘ f) := by
  apply hasLocalExtensionOn_of_locally_contDiffAt
  intro x hx
  obtain ⟨innerExtension⟩ := hf x hx
  obtain ⟨outerExtension⟩ := hg (f x) (himage hx)
  have hinner : ContDiffAt ℝ order innerExtension.extension x :=
    innerExtension.contDiffOn_extension.contDiffAt
      (innerExtension.isOpen_neighborhood.mem_nhds innerExtension.mem_neighborhood)
  have hvalue : innerExtension.extension x = f x :=
    innerExtension.agrees ⟨hx, innerExtension.mem_neighborhood⟩
  have houter : ContDiffAt ℝ order outerExtension.extension (innerExtension.extension x) := by
    rw [hvalue]
    exact outerExtension.contDiffOn_extension.contDiffAt
      (outerExtension.isOpen_neighborhood.mem_nhds outerExtension.mem_neighborhood)
  refine ⟨outerExtension.extension ∘ innerExtension.extension, houter.comp x hinner, ?_⟩
  have htargetNeighborhood : outerExtension.neighborhood ∈ 𝓝 (innerExtension.extension x) := by
    rw [hvalue]
    exact outerExtension.isOpen_neighborhood.mem_nhds outerExtension.mem_neighborhood
  filter_upwards
    [innerExtension.isOpen_neighborhood.mem_nhds innerExtension.mem_neighborhood,
      hinner.continuousAt.preimage_mem_nhds htargetNeighborhood] with y hyInner hyOuter
  intro hy
  have hagrees := innerExtension.agrees ⟨hy, hyInner⟩
  change outerExtension.extension (innerExtension.extension y) = g (f y)
  rw [hagrees]
  exact outerExtension.agrees ⟨himage hy, hagrees ▸ hyOuter⟩

end BoundedUncertainty
