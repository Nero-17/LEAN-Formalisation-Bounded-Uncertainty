import BoundedUncertainty.BundleTangent
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Nonsingularity of the differential on the sphere bundle

These tangent spaces are the hyperplanes of ambient pairs whose normal
component is orthogonal to the marked unit normal.  The differential is
restricted to these hyperplanes, not treated as an invertible ambient map.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The tangent space `E × nᗮ` as an ambient linear subspace of `E × E`. -/
noncomputable def bundleTangentSpace (n : E) : Submodule ℝ (E × E) :=
  ((innerSL ℝ n).comp (ContinuousLinearMap.snd ℝ E E)).ker

@[simp] theorem mem_bundleTangentSpace (n : E) (v : E × E) :
    v ∈ bundleTangentSpace n ↔ inner ℝ n v.2 = 0 := Iff.rfl

/-- Unit-sphere-valuedness on the bundle forces the derivative to preserve
the corresponding tangent hyperplanes, including at base boundary points. -/
theorem fderiv_mem_bundleTangentSpace {X : Set E} {f : E × E → E × E} {x n : E}
    (hX : X ⊆ closure (interior X)) (hx : x ∈ X) (hn : ‖n‖ = 1)
    (hf : ContDiffAt ℝ 1 f (x, n))
    (hunit : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → ‖(f p).2‖ = 1)
    (v : E × E) (hv : v ∈ bundleTangentSpace n) :
    fderiv ℝ f (x, n) v ∈ bundleTangentSpace (f (x, n)).2 := by
  have hzero : ∀ᶠ p in 𝓝 (x, n),
      p ∈ X ×ˢ {n : E | ‖n‖ = 1} → ‖(f p).2‖ ^ 2 - 1 = 0 := by
    filter_upwards [hunit] with p hp hmem
    rw [hp hmem, one_pow, sub_self]
  have hderivative := fderiv_bundle_eq_zero_of_vanishes hX hx hn
    ((hf.snd.norm_sq ℝ).sub contDiffAt_const) hzero v.1 v.2 hv
  have hchain := (hf.differentiableAt one_ne_zero).hasFDerivAt.snd.norm_sq.sub_const 1
  rw [hchain.fderiv] at hderivative
  simp only [two_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply] at hderivative
  change inner ℝ (f (x, n)).2 (fderiv ℝ f (x, n) v).2 +
    inner ℝ (f (x, n)).2 (fderiv ℝ f (x, n) v).2 = 0 at hderivative
  change inner ℝ (f (x, n)).2 (fderiv ℝ f (x, n) v).2 = 0
  linarith

/-- The ambient derivative, restricted to the two intrinsic tangent spaces. -/
noncomputable def bundleDifferential (n u : E) (D : (E × E) →L[ℝ] (E × E))
    (hD : ∀ v ∈ bundleTangentSpace n, D v ∈ bundleTangentSpace u) :
    bundleTangentSpace n →L[ℝ] bundleTangentSpace u :=
  (D.comp (bundleTangentSpace n).subtypeL).codRestrict (bundleTangentSpace u)
    (fun v => hD v v.property)

@[simp] theorem bundleDifferential_apply (n u : E) (D : (E × E) →L[ℝ] (E × E))
    (hD : ∀ v ∈ bundleTangentSpace n, D v ∈ bundleTangentSpace u)
    (v : bundleTangentSpace n) :
    (bundleDifferential n u D hD v : E × E) = D v := rfl

/-- A C1 local left inverse on the actual source bundle gives a left inverse
for the differential in every intrinsic tangent direction. -/
theorem fderiv_bundle_left_inverse {X : Set E} {f g : E × E → E × E} {x n : E}
    (hX : X ⊆ closure (interior X)) (hx : x ∈ X) (hn : ‖n‖ = 1)
    (hf : ContDiffAt ℝ 1 f (x, n)) (hg : ContDiffAt ℝ 1 g (f (x, n)))
    (hleft : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → g (f p) = p)
    (v : E × E) (hv : v ∈ bundleTangentSpace n) :
    fderiv ℝ g (f (x, n)) (fderiv ℝ f (x, n) v) = v := by
  have hzero : ∀ᶠ p in 𝓝 (x, n),
      p ∈ X ×ˢ {n : E | ‖n‖ = 1} → g (f p) - p = 0 := by
    filter_upwards [hleft] with p hp hmem
    rw [hp hmem, sub_self]
  have hderivative := fderiv_bundle_eq_zero_of_vanishes hX hx hn
    ((hg.comp (x, n) hf).sub contDiffAt_id) hzero v.1 v.2 hv
  have hchain := ((hg.differentiableAt one_ne_zero).hasFDerivAt.comp (x, n)
    (hf.differentiableAt one_ne_zero).hasFDerivAt).sub (hasFDerivAt_id (x, n))
  change fderiv ℝ (g ∘ f - id) (x, n) v = 0 at hderivative
  rw [hchain.fderiv] at hderivative
  exact sub_eq_zero.mp hderivative

variable [FiniteDimensional ℝ E]

/-- The intrinsic tangent space has codimension one in the ambient product. -/
theorem finrank_bundleTangentSpace_add_one (n : E) (hn : ‖n‖ = 1) :
    Module.finrank ℝ (bundleTangentSpace n) + 1 = Module.finrank ℝ (E × E) := by
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro hzero
  have heq := congrArg (fun D : (E × E) →ₗ[ℝ] ℝ => D (0, n)) hzero
  simp [hn] at heq

/-- In ambient dimension `d`, the sphere-bundle tangent dimension is `2d-1`. -/
theorem finrank_bundleTangentSpace (n : E) (hn : ‖n‖ = 1) :
    Module.finrank ℝ (bundleTangentSpace n) = 2 * Module.finrank ℝ E - 1 := by
  have hdimension := finrank_bundleTangentSpace_add_one n hn
  rw [Module.finrank_prod] at hdimension
  omega

/-- A local inverse on the source bundle makes its intrinsic differential
bijective between the two equal-dimensional tangent hyperplanes. -/
theorem bundleDifferential_bijective_of_local_left_inverse
    {X : Set E} {f g : E × E → E × E} {x n : E}
    (hX : X ⊆ closure (interior X)) (hx : x ∈ X) (hn : ‖n‖ = 1)
    (hf : ContDiffAt ℝ 1 f (x, n)) (hg : ContDiffAt ℝ 1 g (f (x, n)))
    (hunit : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → ‖(f p).2‖ = 1)
    (hleft : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → g (f p) = p) :
    Function.Bijective (bundleDifferential n (f (x, n)).2 (fderiv ℝ f (x, n))
      (fderiv_mem_bundleTangentSpace hX hx hn hf hunit)) := by
  have hinjective : Function.Injective
      (bundleDifferential n (f (x, n)).2 (fderiv ℝ f (x, n))
        (fderiv_mem_bundleTangentSpace hX hx hn hf hunit)) := by
    intro v w heq
    apply Subtype.ext
    have hderivative := congrArg (fun t : bundleTangentSpace (f (x, n)).2 => (t : E × E)) heq
    have hrecovered := congrArg (fderiv ℝ g (f (x, n))) hderivative
    simpa only [bundleDifferential_apply,
      fderiv_bundle_left_inverse hX hx hn hf hg hleft v v.property,
      fderiv_bundle_left_inverse hX hx hn hf hg hleft w w.property] using hrecovered
  refine ⟨hinjective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinjective⟩
  have hinput := finrank_bundleTangentSpace_add_one n hn
  have houtput := finrank_bundleTangentSpace_add_one (f (x, n)).2
    (hunit.self_of_nhds ⟨hx, hn⟩)
  omega

/-- The intrinsic differential as a continuous linear equivalence. -/
noncomputable def bundleTangentEquivOfLocalInverse
    {X : Set E} {f g : E × E → E × E} {x n : E}
    (hX : X ⊆ closure (interior X)) (hx : x ∈ X) (hn : ‖n‖ = 1)
    (hf : ContDiffAt ℝ 1 f (x, n)) (hg : ContDiffAt ℝ 1 g (f (x, n)))
    (hunit : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → ‖(f p).2‖ = 1)
    (hleft : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → g (f p) = p) :
    bundleTangentSpace n ≃L[ℝ] bundleTangentSpace (f (x, n)).2 :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective
    (bundleDifferential n (f (x, n)).2 (fderiv ℝ f (x, n))
      (fderiv_mem_bundleTangentSpace hX hx hn hf hunit)).toLinearMap
    (bundleDifferential_bijective_of_local_left_inverse hX hx hn hf hg hunit hleft))

@[simp] theorem bundleTangentEquivOfLocalInverse_apply
    {X : Set E} {f g : E × E → E × E} {x n : E}
    (hX : X ⊆ closure (interior X)) (hx : x ∈ X) (hn : ‖n‖ = 1)
    (hf : ContDiffAt ℝ 1 f (x, n)) (hg : ContDiffAt ℝ 1 g (f (x, n)))
    (hunit : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → ‖(f p).2‖ = 1)
    (hleft : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → g (f p) = p)
    (v : bundleTangentSpace n) :
    (bundleTangentEquivOfLocalInverse hX hx hn hf hg hunit hleft v : E × E) =
      fderiv ℝ f (x, n) v := rfl

end BoundedUncertainty
