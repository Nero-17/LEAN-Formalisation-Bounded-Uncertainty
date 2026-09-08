import BoundedUncertainty.HigherDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Higher regularity of the exponential formula

The normal-update radicand is strictly positive when the gradient has norm
less than one, including when that gradient is zero. Its square norm is treated
as an inner product, so no differentiability of the norm at zero is assumed.
Local extensions of the radius and gradient then give a local extension of the
full exponential formula. Only unit inputs are asserted to represent the paper's
normal bundle; the larger ambient-input theorem asserts regularity alone.
-/

namespace BoundedUncertainty

open Set Filter Topology

section Restriction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restricting the domain preserves the same local ambient extensions. -/
theorem HasLocalExtensionOn.mono_domain {order : ℕ} {X Y : Set E} {f : E → F}
    (h : HasLocalExtensionOn order X f) (hYX : Y ⊆ X) :
    HasLocalExtensionOn order Y f := by
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

end Restriction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a gradient of norm below one the raw normal-update formula is smooth
in both ambient vector variables, even at a zero gradient. -/
theorem contDiffAt_normalUpdate (order : WithTop ℕ∞) (gradient n : E)
    (hgradient : ‖gradient‖ < 1) :
    ContDiffAt ℝ order (fun p : E × E => normalUpdate p.1 p.2) (gradient, n) := by
  have hinner : ContDiffAt ℝ order
      (fun p : E × E => inner ℝ p.2 p.1) (gradient, n) :=
    contDiffAt_snd.inner ℝ contDiffAt_fst
  have hsquare : ContDiffAt ℝ order
      (fun p : E × E => ‖p.1‖ ^ 2) (gradient, n) := by
    simpa only [real_inner_self_eq_norm_sq] using
      (contDiffAt_fst.inner ℝ contDiffAt_fst :
        ContDiffAt ℝ order (fun p : E × E => inner ℝ p.1 p.1) (gradient, n))
  have hsqrt : ContDiffAt ℝ order
      (fun p : E × E => Real.sqrt ((inner ℝ p.2 p.1) ^ 2 - ‖p.1‖ ^ 2 + 1))
      (gradient, n) :=
    (((hinner.pow 2).sub hsquare).add contDiffAt_const).sqrt
      (normalUpdate_radicand_pos gradient n hgradient).ne'
  exact ((hinner.add hsqrt).smul contDiffAt_snd).sub contDiffAt_fst

/-- Smooth radius and gradient representatives make the exponential formula
smooth near a centre whose gradient has norm below one. -/
theorem contDiffAt_exponentialMap {order : WithTop ℕ∞} (ε : E → ℝ) (gradient : E → E)
    (y n : E) (hε : ContDiffAt ℝ order ε y) (hgradient : ContDiffAt ℝ order gradient y)
    (hbound : ‖gradient y‖ < 1) :
    ContDiffAt ℝ order (exponentialMap ε gradient) (y, n) := by
  have hnormal : ContDiffAt ℝ order
      (fun p : E × E => normalUpdate (gradient p.1) p.2) (y, n) :=
    (contDiffAt_normalUpdate order (gradient y) n hbound).comp (y, n)
      ((hgradient.comp (y, n) contDiffAt_fst).prodMk contDiffAt_snd)
  exact (contDiffAt_fst.add
    ((hε.comp (y, n) contDiffAt_fst).smul hnormal)).prodMk hnormal

/-- Local extensions of a radius and a vector field produce local extensions
of the exponential formula on `X × E`. No unit-output statement is made here. -/
theorem hasLocalExtensionOn_exponentialMap {order : ℕ} {X : Set E}
    (ε : E → ℝ) (gradient : E → E)
    (hε : HasLocalExtensionOn order X ε)
    (hgradient : HasLocalExtensionOn order X gradient)
    (hbound : ∀ y ∈ X, ‖gradient y‖ < 1) :
    HasLocalExtensionOn order (X ×ˢ (Set.univ : Set E)) (exponentialMap ε gradient) := by
  intro p hp
  obtain ⟨radiusExtension⟩ := hε p.1 hp.1
  obtain ⟨gradientExtension⟩ := hgradient p.1 hp.1
  have hcontdiff : ContDiffAt ℝ order
      (exponentialMap radiusExtension.extension gradientExtension.extension) p := by
    apply contDiffAt_exponentialMap
    · exact radiusExtension.contDiffOn_extension.contDiffAt
        (radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood)
    · exact gradientExtension.contDiffOn_extension.contDiffAt
        (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood)
    · rw [gradientExtension.agrees ⟨hp.1, gradientExtension.mem_neighborhood⟩]
      exact hbound p.1 hp.1
  obtain ⟨U, hUnhds, hUcontdiff⟩ := hcontdiff.contDiffOn le_rfl (by simp)
  have hneighborhood :
      U ∩ Prod.fst ⁻¹' radiusExtension.neighborhood ∩
        Prod.fst ⁻¹' gradientExtension.neighborhood ∈ 𝓝 p :=
    inter_mem (inter_mem hUnhds
      (continuous_fst.continuousAt.preimage_mem_nhds
        (radiusExtension.isOpen_neighborhood.mem_nhds radiusExtension.mem_neighborhood)))
      (continuous_fst.continuousAt.preimage_mem_nhds
        (gradientExtension.isOpen_neighborhood.mem_nhds gradientExtension.mem_neighborhood))
  obtain ⟨V, hVsubset, hVopen, hpV⟩ := mem_nhds_iff.mp hneighborhood
  refine ⟨{
    neighborhood := V
    isOpen_neighborhood := hVopen
    mem_neighborhood := hpV
    extension := exponentialMap radiusExtension.extension gradientExtension.extension
    contDiffOn_extension := hUcontdiff.mono (fun q hq => (hVsubset hq).1.1)
    agrees := ?_
  }⟩
  intro q hq
  have hradius := radiusExtension.agrees ⟨hq.1.1, (hVsubset hq.2).1.2⟩
  have hgradientValue := gradientExtension.agrees ⟨hq.1.1, (hVsubset hq.2).2⟩
  simp only [exponentialMap, hradius, hgradientValue]

variable [CompleteSpace E] {r s : ℕ}

/-- With the true canonical radius gradient, the exponential formula has local
`C^(r-1)` extensions for all ambient normal coordinates. -/
theorem SetValuedSystem.hasLocalExtensionOn_exponentialMap_on_domain_prod_univ
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    HasLocalExtensionOn (r - 1) (system.domain ×ˢ (Set.univ : Set E))
      (exponentialMap system.radius system.radiusGradientOnAmbient) :=
  hasLocalExtensionOn_exponentialMap system.radius system.radiusGradientOnAmbient
    (system.radius_extension.of_le (Nat.sub_le r 1))
    system.hasLocalExtensionOn_radiusGradientOnAmbient
    hcontraction.norm_radiusGradientOnAmbient

/-- The higher-regularity assertion for the paper's actual exponential formula
on domain points and unit normals, with the original pointwise contraction. -/
theorem SetValuedSystem.hasLocalExtensionOn_exponentialMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    HasLocalExtensionOn (r - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
      (exponentialMap system.radius system.radiusGradientOnAmbient) :=
  (system.hasLocalExtensionOn_exponentialMap_on_domain_prod_univ hcontraction).mono_domain
    (fun _ hp => ⟨hp.1, Set.mem_univ _⟩)

end BoundedUncertainty
