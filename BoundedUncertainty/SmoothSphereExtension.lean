import BoundedUncertainty.SmoothLocalExtension
import BoundedUncertainty.BundleSphereExtension

/-! The sphere-valued extension convention, on one fixed C-infinity neighborhood. -/

namespace BoundedUncertainty

open Set Filter Topology
open scoped ContDiff

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalize the same fixed smooth witness on one smaller open neighborhood.
The resulting extension takes values in the sphere bundle everywhere there. -/
theorem SmoothLocalExtensionAt.exists_sphere_valued_extension {X : Set A}
    {f : A → E × E} {x : A} (extension : SmoothLocalExtensionAt X f x) (hx : x ∈ X)
    (hunit : ∀ y ∈ X, ‖(f y).2‖ = 1) :
    ∃ sphereExtension : SmoothLocalExtensionAt X f x,
      ∀ y ∈ sphereExtension.neighborhood, ‖(sphereExtension.extension y).2‖ = 1 := by
  have hvalue := extension.agrees ⟨hx, extension.mem_neighborhood⟩
  have hnonzero : (extension.extension x).2 ≠ 0 := by
    rw [hvalue]
    exact norm_ne_zero_iff.mp ((hunit x hx).trans_ne one_ne_zero)
  have hcontinuous : ContinuousAt extension.extension x :=
    extension.contDiffOn_extension.continuousOn.continuousAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  have havoids : ∀ᶠ y in 𝓝 x, (extension.extension y).2 ≠ 0 :=
    hcontinuous.snd (isOpen_compl_singleton.mem_nhds hnonzero)
  obtain ⟨V, hVsubset, hVopen, hxV⟩ := mem_nhds_iff.mp
    (inter_mem (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood) havoids)
  refine ⟨{
    neighborhood := V
    isOpen_neighborhood := hVopen
    mem_neighborhood := hxV
    extension := normalizeBundleOutput ∘ extension.extension
    contDiffOn_extension := ContDiffOn.normalizeBundleOutput
      (extension.contDiffOn_extension.mono (fun y hy => (hVsubset hy).1))
      (fun y hy => (hVsubset hy).2)
    agrees := ?_
  }, ?_⟩
  · intro y hy
    change normalizeBundleOutput (extension.extension y) = f y
    rw [extension.agrees ⟨hy.1, (hVsubset hy.2).1⟩]
    exact normalizeBundleOutput_eq_of_unit (f y) (hunit y hy.1)
  · intro y hy
    exact norm_normalizeBundleOutput_snd (extension.extension y) (hVsubset hy).2

/-- A smoothly extendible sphere-valued map has a fixed smooth sphere-valued
neighborhood extension at every source point. -/
theorem HasSmoothLocalExtensionOn.exists_sphere_valued_extension {X : Set A}
    {f : A → E × E} (h : HasSmoothLocalExtensionOn X f)
    (hunit : ∀ y ∈ X, ‖(f y).2‖ = 1) (x : A) (hx : x ∈ X) :
    ∃ extension : SmoothLocalExtensionAt X f x,
      ∀ y ∈ extension.neighborhood, ‖(extension.extension y).2‖ = 1 := by
  obtain ⟨extension⟩ := h x hx
  exact extension.exists_sphere_valued_extension hx hunit

end BoundedUncertainty
