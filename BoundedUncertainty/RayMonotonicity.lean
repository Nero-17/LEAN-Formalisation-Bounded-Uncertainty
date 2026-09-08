import BoundedUncertainty.BoundaryMap
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Differentiation along a ray that stays in the domain. Only the given local
extensions are differentiated; the ambient representative of the radius is
not assumed differentiable. This is the analytic injectivity step in 3.14.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

theorem SetValuedSystem.hasDerivAt_radius_ray
    (system : SetValuedSystem (E := E) r s) (z u : E) (t : ℝ)
    (hray : ∀ᶠ q in 𝓝 t, z - q • u ∈ system.domain) :
    HasDerivAt (fun q : ℝ => system.radius (z - q • u))
      (-inner ℝ (system.radiusGradientOnAmbient (z - t • u)) u) t := by
  have ht : z - t • u ∈ system.domain := hray.self_of_nhds
  obtain ⟨extension⟩ := system.radius_extension (z - t • u) ht
  have hcontdiff : ContDiffOn ℝ 1 extension.extension extension.neighborhood :=
    extension.contDiffOn_extension.of_le (by exact_mod_cast system.radius_order_pos)
  have hdiff := hcontdiff.differentiableOn_one.differentiableAt
    (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  have hgradient : system.radiusGradientOnAmbient (z - t • u) =
      gradient extension.extension (z - t • u) := by
    exact (system.radiusGradientOnAmbient_apply ⟨z - t • u, ht⟩).trans
      (system.radiusGradient_eq_extension system.radius_order_pos extension
        ⟨z - t • u, ht⟩ extension.mem_neighborhood)
  have hderiv : HasDerivAt (fun q : ℝ => extension.extension (z - q • u))
      (-inner ℝ (system.radiusGradientOnAmbient (z - t • u)) u) t := by
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const u).const_sub z)
    simpa only [hgradient, one_smul, map_neg,
      hdiff.hasGradientAt.fderiv_apply, inner_neg_right] using hcomp
  apply hderiv.congr_of_eventuallyEq
  have hcontinuous : Continuous (fun q : ℝ => z - q • u) := by fun_prop
  filter_upwards [hray, hcontinuous.continuousAt.preimage_mem_nhds
    (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)] with q hq hqU
  exact (extension.agrees ⟨hq, hqU⟩).symm

theorem SetValuedSystem.strictMonoOn_radius_ray
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (z u : E) (hu : ‖u‖ = 1) (a b : ℝ)
    (hray : ∀ q ∈ Icc a b, z - q • u ∈ system.domain) :
    StrictMonoOn (fun q : ℝ => q - system.radius (z - q • u)) (Icc a b) := by
  have hcontinuous : Continuous (fun q : ℝ => z - q • u) := by fun_prop
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    (continuousOn_id.sub (system.radius_extension.continuousOn.comp
      hcontinuous.continuousOn hray))
  intro t ht
  have hderiv := (hasDerivAt_id t).sub (system.hasDerivAt_radius_ray z u t (by
    filter_upwards [isOpen_interior.mem_nhds ht] with q hq
    exact hray q (interior_subset hq)))
  change 0 < deriv (id - fun q : ℝ => system.radius (z - q • u)) t
  rw [hderiv.deriv]
  have hbound := neg_le_of_abs_le
    (abs_real_inner_le_norm (system.radiusGradientOnAmbient (z - t • u)) u)
  rw [hu, mul_one] at hbound
  have hlt := hcontraction.norm_radiusGradientOnAmbient
    (z - t • u) (hray t (interior_subset ht))
  linarith

end BoundedUncertainty
