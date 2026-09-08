import BoundedUncertainty.SmoothLocalExtension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
A smooth map injective on a compact domain has an actual inverse on its
image. If its differential is nonsingular on an open neighborhood of the
domain, that same inverse has one smooth local extension at every image
point. Compactness excludes preimages outside the chosen IFT source.
-/

namespace BoundedUncertainty

open Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_smooth_openPartialHomeomorph (f : E → E) (hf : ContDiff ℝ ∞ f)
    (U : Set E) (hU : IsOpen U)
    (hnonsingular : ∀ x ∈ U, ∃ derivative : E ≃L[ℝ] E,
      HasFDerivAt f (derivative : E →L[ℝ] E) x)
    (x : E) (hx : x ∈ U) :
    ∃ coordinates : OpenPartialHomeomorph E E,
      (coordinates : E → E) = f ∧ x ∈ coordinates.source ∧
        coordinates.source ⊆ U ∧ ContDiffOn ℝ ∞ coordinates.symm coordinates.target := by
  obtain ⟨derivative, hderivative⟩ := hnonsingular x hx
  let coordinates := (hf.contDiffAt.toOpenPartialHomeomorph f hderivative (by simp)).restrOpen U hU
  have hcoordinates : (coordinates : E → E) = f := rfl
  refine ⟨coordinates, hcoordinates, ?_, ?_, ?_⟩
  · exact ⟨hf.contDiffAt.mem_toOpenPartialHomeomorph_source hderivative (by simp), hx⟩
  · exact fun _ hp => hp.2
  · intro w hw
    have hsource : coordinates.symm w ∈ coordinates.source := coordinates.map_target hw
    obtain ⟨inverseDerivative, hinverseDerivative⟩ := hnonsingular (coordinates.symm w) hsource.2
    apply (coordinates.contDiffAt_symm (f₀' := inverseDerivative) hw ?_ ?_).contDiffWithinAt
    · rw [hcoordinates]
      exact hinverseDerivative
    · rw [hcoordinates]
      exact hf.contDiffAt

theorem hasSmoothLocalExtensionOn_invFunOn_of_compact (f : E → E) (X : Set E)
    (hcompact : IsCompact X) (hf : ContDiff ℝ ∞ f) (hinjective : Set.InjOn f X)
    (U : Set E) (hU : IsOpen U) (hXU : X ⊆ U)
    (hnonsingular : ∀ x ∈ U, ∃ derivative : E ≃L[ℝ] E,
      HasFDerivAt f (derivative : E →L[ℝ] E) x) :
    HasSmoothLocalExtensionOn (f '' X) (Function.invFunOn f X) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨coordinates, hcoordinates, hxsource, _, hsmoothInverse⟩ :=
    exists_smooth_openPartialHomeomorph f hf U hU hnonsingular x (hXU hx)
  have hclosed : IsClosed (f '' (X \ coordinates.source)) :=
    ((hcompact.diff coordinates.open_source).image hf.continuous).isClosed
  have hnotimage : f x ∉ f '' (X \ coordinates.source) := by
    rintro ⟨y, hy, hxy⟩
    have heq := hinjective hy.1 hx hxy
    exact hy.2 (heq.symm ▸ hxsource)
  refine ⟨{
    neighborhood := coordinates.target ∩ (f '' (X \ coordinates.source))ᶜ
    isOpen_neighborhood := coordinates.open_target.inter hclosed.isOpen_compl
    mem_neighborhood := ⟨?_, hnotimage⟩
    extension := coordinates.symm
    contDiffOn_extension := hsmoothInverse.mono Set.inter_subset_left
    agrees := ?_ }⟩
  · rw [← hcoordinates]
    exact coordinates.map_source hxsource
  · intro w hw
    have hinverseX : Function.invFunOn f X w ∈ X := Function.invFunOn_mem hw.1
    have hinverseValue : f (Function.invFunOn f X w) = w := Function.invFunOn_eq hw.1
    have hinverseSource : Function.invFunOn f X w ∈ coordinates.source := by
      by_contra houtside
      exact hw.2.2 ⟨Function.invFunOn f X w, ⟨hinverseX, houtside⟩, hinverseValue⟩
    calc
      coordinates.symm w = coordinates.symm (f (Function.invFunOn f X w)) :=
        congrArg coordinates.symm hinverseValue.symm
      _ = coordinates.symm (coordinates (Function.invFunOn f X w)) :=
        congrArg coordinates.symm (congrFun hcoordinates (Function.invFunOn f X w)).symm
      _ = Function.invFunOn f X w := coordinates.left_inv hinverseSource

/-- The same chosen inverse supplies every finite regularity order in Definition 3.1. -/
noncomputable def ambientDiffeomorphismOn_of_compact_smooth
    (f : E → E) (X : Set E) (hcompact : IsCompact X) (hf : ContDiff ℝ ∞ f)
    (hinjective : Set.InjOn f X) (U : Set E) (hU : IsOpen U) (hXU : X ⊆ U)
    (hnonsingular : ∀ x ∈ U, ∃ derivative : E ≃L[ℝ] E,
      HasFDerivAt f (derivative : E →L[ℝ] E) x)
    (order : ℕ) : AmbientDiffeomorphismOn order X f where
  inverse := Function.invFunOn f X
  inverse_mapsTo := fun _ hy => Function.invFunOn_mem hy
  left_inverse := hinjective.leftInvOn_invFunOn
  forward_extension x _ := ⟨{
    neighborhood := univ
    isOpen_neighborhood := isOpen_univ
    mem_neighborhood := mem_univ x
    extension := f
    contDiffOn_extension := hf.contDiffOn.of_le
      (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)
    agrees := fun _ _ => rfl }⟩
  inverse_extension := (hasSmoothLocalExtensionOn_invFunOn_of_compact f X hcompact hf
    hinjective U hU hXU hnonsingular).toHasLocalExtensionOn order
  nonsingular x hx := by
    obtain ⟨derivative, hderivative⟩ := hnonsingular x (hXU hx)
    exact ⟨{
      neighborhood := univ
      isOpen_neighborhood := isOpen_univ
      mem_neighborhood := mem_univ x
      extension := f
      contDiffOn_extension := hf.contDiffOn.of_le
        (show (order : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)
      agrees := fun _ _ => rfl
      derivative := derivative
      hasFDerivAt_extension := hderivative }⟩

end BoundedUncertainty
