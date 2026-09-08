import BoundedUncertainty.LocalExtensionOperations
import BoundedUncertainty.HigherExponential

/-!
# Local extensions with values in the sphere bundle

An ambient extension whose original values have a unit second coordinate can
be normalized in a neighborhood of each source point. This produces a genuine
sphere-valued local extension without altering its values on the source set.
The normalization lemmas allow every mathlib regularity order, including infinity.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalize only the normal coordinate of an ambient pair. -/
noncomputable def normalizeBundleOutput (p : E × E) : E × E :=
  (p.1, ‖p.2‖⁻¹ • p.2)

theorem normalizeBundleOutput_eq_of_unit (p : E × E) (hp : ‖p.2‖ = 1) :
    normalizeBundleOutput p = p := by
  simp only [normalizeBundleOutput, hp, inv_one, one_smul, Prod.eta]

theorem norm_normalizeBundleOutput_snd (p : E × E) (hp : p.2 ≠ 0) :
    ‖(normalizeBundleOutput p).2‖ = 1 := norm_smul_inv_norm hp

/-- Normalization is smooth at every pair with nonzero normal coordinate. -/
theorem contDiffAt_normalizeBundleOutput (order : WithTop ℕ∞) (p : E × E)
    (hp : p.2 ≠ 0) : ContDiffAt ℝ order normalizeBundleOutput p :=
  contDiffAt_fst.prodMk
    (((contDiffAt_snd.norm ℝ hp).inv (norm_ne_zero_iff.mpr hp)).smul contDiffAt_snd)

theorem contDiffOn_normalizeBundleOutput (order : WithTop ℕ∞) :
    ContDiffOn ℝ order (normalizeBundleOutput : E × E → E × E) {p | p.2 ≠ 0} :=
  fun p hp => (contDiffAt_normalizeBundleOutput order p hp).contDiffWithinAt

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The order here includes `∞`, so the same fixed smooth extension can be normalized. -/
theorem ContDiffOn.normalizeBundleOutput {order : WithTop ℕ∞} {f : A → E × E} {U : Set A}
    (hf : ContDiffOn ℝ order f U) (hnonzero : ∀ x ∈ U, (f x).2 ≠ 0) :
    ContDiffOn ℝ order (normalizeBundleOutput ∘ f) U :=
  fun x hx => (contDiffAt_normalizeBundleOutput order (f x) (hnonzero x hx)).comp_contDiffWithinAt
    x (hf x hx)

/-- Every finite-order ambient extension of a sphere-bundle-valued map can
be replaced by one whose values lie in that bundle on its entire neighborhood. -/
theorem LocalExtensionAt.exists_sphere_valued_extension {order : ℕ} {X : Set A}
    {f : A → E × E} {x : A} (extension : LocalExtensionAt order X f x) (hx : x ∈ X)
    (hunit : ∀ y ∈ X, ‖(f y).2‖ = 1) :
    ∃ sphereExtension : LocalExtensionAt order X f x,
      ∀ y ∈ sphereExtension.neighborhood, ‖(sphereExtension.extension y).2‖ = 1 := by
  have hvalue := extension.agrees ⟨hx, extension.mem_neighborhood⟩
  have hnonzero : (extension.extension x).2 ≠ 0 := by
    rw [hvalue]
    exact norm_ne_zero_iff.mp ((hunit x hx).trans_ne one_ne_zero)
  have hsmooth : ContDiffAt ℝ order extension.extension x :=
    extension.contDiffOn_extension.contDiffAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  have havoids : ∀ᶠ y in 𝓝 x, (extension.extension y).2 ≠ 0 :=
    hsmooth.continuousAt.snd (isOpen_compl_singleton.mem_nhds hnonzero)
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

end BoundedUncertainty
