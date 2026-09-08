import BoundedUncertainty.HigherBoundaryInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The intrinsic differential on the unit sphere bundle

The tangent space at `(x,n)` is `E × nᗮ`, independently of any boundary of the
regular closed base set.  A locally C1 function vanishing on the base times
the unit sphere has zero differential in all these directions.  This is the
extension-independence statement needed for the intrinsic bundle differential.
-/

namespace BoundedUncertainty

open Set Filter Topology

section RegularClosed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A locally C1 function vanishing on a regular closed set has zero derivative there. -/
theorem fderiv_eq_zero_of_contDiffAt_vanishes {X : Set E} {f : E → F} {x : E}
    (hX : X ⊆ closure (interior X)) (hx : x ∈ X) (hf : ContDiffAt ℝ 1 f x)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ X → f y = 0) : fderiv ℝ f x = 0 := by
  obtain ⟨U, hUnhds, hUsmooth⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVsubset, hVopen, hxV⟩ := mem_nhds_iff.mp (inter_mem hUnhds hzero)
  have heq := fderiv_eq_of_contDiffOn_eqOn hX hVopen
    (hUsmooth.mono (fun y hy => (hVsubset hy).1)) contDiffOn_const
    (fun y hy => (hVsubset hy.2).2 hy.1) hx hxV
  simpa using heq

end RegularClosed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A tangent vector is realized by a differentiable curve on the unit sphere. -/
theorem hasDerivAt_normalized_tangent_curve (n w : E) (hn : ‖n‖ = 1)
    (hw : inner ℝ n w = 0) :
    HasDerivAt (fun t : ℝ => ‖n + t • w‖⁻¹ • (n + t • w)) w 0 := by
  have hline : HasDerivAt (fun t : ℝ => n + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add n
  have hnorm : HasDerivAt (fun t : ℝ => ‖n + t • w‖) 0 0 := by
    simpa [hn, hw] using hline.norm_sq.sqrt (by simp [hn])
  simpa only [Pi.smul_apply, Pi.inv_apply, zero_smul, add_zero, hn, inv_one,
    neg_zero, zero_div, one_smul, zero_add] using (hnorm.inv (by simp [hn])).smul hline

/-- Every point of the normalized tangent curve is a unit vector. -/
theorem norm_normalized_tangent_curve (n w : E) (hn : ‖n‖ = 1)
    (hw : inner ℝ n w = 0) (t : ℝ) :
    ‖‖n + t • w‖⁻¹ • (n + t • w)‖ = 1 := by
  have hnonzero : n + t • w ≠ 0 := by
    intro hzero
    have hinner := congrArg (inner ℝ n) hzero
    simp [inner_add_right, real_inner_smul_right, hn, hw] at hinner
  exact norm_smul_inv_norm hnonzero

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The differential of a locally vanishing bundle function annihilates every
base direction and every sphere-tangent direction, including at base boundary points. -/
theorem fderiv_bundle_eq_zero_of_vanishes {X : Set E} {f : E × E → F}
    {x n : E} (hX : X ⊆ closure (interior X)) (hx : x ∈ X) (hn : ‖n‖ = 1)
    (hf : ContDiffAt ℝ 1 f (x, n))
    (hzero : ∀ᶠ p in 𝓝 (x, n), p ∈ X ×ˢ {n : E | ‖n‖ = 1} → f p = 0)
    (v w : E) (hw : inner ℝ n w = 0) : fderiv ℝ f (x, n) (v, w) = 0 := by
  have hbaseSmooth : ContDiffAt ℝ 1 (fun y : E => f (y, n)) x :=
    hf.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hbaseZero : ∀ᶠ y in 𝓝 x, y ∈ X → f (y, n) = 0 := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt hzero] with y hy hyX
    exact hy ⟨hyX, hn⟩
  have hbaseDerivative := fderiv_eq_zero_of_contDiffAt_vanishes hX hx hbaseSmooth hbaseZero
  have hbaseChain : HasFDerivAt (fun y : E => f (y, n))
      ((fderiv ℝ f (x, n)).comp ((ContinuousLinearMap.id ℝ E).prod 0)) x :=
    (hf.differentiableAt one_ne_zero).hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const n x))
  have hbase : fderiv ℝ f (x, n) (v, 0) = 0 := by
    have heq := hbaseChain.fderiv
    rw [hbaseDerivative] at heq
    exact (congrArg (fun D : E →L[ℝ] F => D v) heq).symm
  have hcurve : HasDerivAt
      (fun t : ℝ => (x, ‖n + t • w‖⁻¹ • (n + t • w))) (0, w) 0 :=
    (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_normalized_tangent_curve n w hn hw)
  have hcurveZero : ∀ᶠ t in 𝓝 (0 : ℝ),
      f (x, ‖n + t • w‖⁻¹ • (n + t • w)) = 0 := by
    have hnear := hcurve.continuousAt (by
      simpa only [zero_smul, add_zero, hn, inv_one, one_smul] using hzero)
    filter_upwards [hnear] with t ht
    exact ht ⟨hx, norm_normalized_tangent_curve n w hn hw t⟩
  have hcurveChain : HasDerivAt
      (fun t : ℝ => f (x, ‖n + t • w‖⁻¹ • (n + t • w)))
      (fderiv ℝ f (x, n) (0, w)) 0 :=
    (hf.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hcurve (by simp [hn])
  have htangent : fderiv ℝ f (x, n) (0, w) = 0 :=
    hcurveChain.unique ((hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq hcurveZero)
  have hsplit : (v, w) = (v, 0) + (0, w) := by simp
  rw [hsplit, map_add, hbase, htangent, add_zero]

end BoundedUncertainty
