import BoundedUncertainty.HigherLinearLift
import BoundedUncertainty.LinearLiftHomeomorph

/-!
# Higher regularity of the inverse linear lift

The inverse position is the given local inverse of the deterministic map.
The inverse normal uses the normalized transpose of the actual differential at
that recovered source point. The construction only uses local extensions on
the actual deterministic image; it does not require that image to be closed.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The transpose-normalization formula used for the inverse linear lift. -/
noncomputable def transposeLiftFormula (f : E → E) (D : E → E →L[ℝ] E) (p : E × E) : E × E :=
  (f p.1,
    ‖ContinuousLinearMap.adjoint (D p.1) p.2‖⁻¹ • ContinuousLinearMap.adjoint (D p.1) p.2)

theorem contDiffAt_transposeLiftFormula {order : WithTop ℕ∞}
    (f : E → E) (D : E → E →L[ℝ] E) (x n : E) (T : E ≃L[ℝ] E)
    (hf : ContDiffAt ℝ order f x) (hD : ContDiffAt ℝ order D x)
    (hvalue : D x = (T : E →L[ℝ] E)) (hn : ‖n‖ = 1) :
    ContDiffAt ℝ order (transposeLiftFormula f D) (x, n) := by
  have hoperator : ContDiffAt ℝ order
      (fun p : E × E => ContinuousLinearMap.adjoint (D p.1)) (x, n) :=
    ContinuousLinearMap.adjoint.contDiff.contDiffAt.comp (x, n)
      (hD.comp (x, n) contDiffAt_fst)
  have hvector : ContDiffAt ℝ order
      (fun p : E × E => ContinuousLinearMap.adjoint (D p.1) p.2) (x, n) :=
    hoperator.clm_apply contDiffAt_snd
  have hnonzero : ContinuousLinearMap.adjoint (D x) n ≠ 0 := by
    rw [hvalue]
    exact linearMap_unit_ne_zero (inverseTranspose T).symm hn
  exact (hf.comp (x, n) contDiffAt_fst).prodMk
    (((hvector.norm ℝ hnonzero).inv (norm_ne_zero_iff.mpr hnonzero)).smul hvector)

variable {r s : ℕ}

/-- The inverse linear lift as an ambient representative. It uses the true
source differential after recovering the source point. -/
noncomputable def SetValuedSystem.linearLiftInverseOnAmbient
    (system : SetValuedSystem (E := E) r s) : E × E → E × E :=
  transposeLiftFormula system.diffeomorphism.inverse
    (system.mapDerivativeOnAmbient ∘ system.diffeomorphism.inverse)

/-- On the actual image bundle the representative is exactly the inverse of L. -/
theorem SetValuedSystem.linearLiftInverseOnAmbient_apply
    (system : SetValuedSystem (E := E) r s)
    (p : (system.map '' system.domain) × {n : E // ‖n‖ = 1}) :
    system.linearLiftInverseOnAmbient ((p.1 : E), (p.2 : E)) =
      (((system.linearLiftHomeomorph.symm p).1 : E),
        ((system.linearLiftHomeomorph.symm p).2 : E)) := by
  unfold SetValuedSystem.linearLiftInverseOnAmbient transposeLiftFormula
  change (system.diffeomorphism.inverse p.1,
    ‖ContinuousLinearMap.adjoint
        (system.mapDerivativeOnAmbient (system.mapImageHomeomorph.symm p.1)) (p.2 : E)‖⁻¹ •
      ContinuousLinearMap.adjoint
        (system.mapDerivativeOnAmbient (system.mapImageHomeomorph.symm p.1)) (p.2 : E)) = _
  rw [system.mapDerivativeOnAmbient_eq_derivativeEquiv (system.mapImageHomeomorph.symm p.1)]
  rfl

/-- The inverse linear lift has local `C^(s-1)` ambient extensions on the actual
image bundle, even when the deterministic image is not closed. -/
theorem SetValuedSystem.hasLocalExtensionOn_linearLiftInverseOnAmbient
    (system : SetValuedSystem (E := E) r s) :
    HasLocalExtensionOn (s - 1) ((system.map '' system.domain) ×ˢ {n : E | ‖n‖ = 1})
      system.linearLiftInverseOnAmbient := by
  have hderivativeField : HasLocalExtensionOn (s - 1) (system.map '' system.domain)
      (system.mapDerivativeOnAmbient ∘ system.diffeomorphism.inverse) :=
    system.hasLocalExtensionOn_mapDerivativeOnAmbient.comp
      (system.diffeomorphism.inverse_extension.of_le (Nat.sub_le s 1))
      system.diffeomorphism.inverse_mapsTo
  apply hasLocalExtensionOn_of_locally_contDiffAt
  intro p hp
  obtain ⟨inverseExtension⟩ := system.diffeomorphism.inverse_extension p.1 hp.1
  obtain ⟨derivativeExtension⟩ := hderivativeField p.1 hp.1
  have hinverse : ContDiffAt ℝ (s - 1 : ℕ) inverseExtension.extension p.1 :=
    (inverseExtension.contDiffOn_extension.of_le (by exact_mod_cast Nat.sub_le s 1)).contDiffAt
      (inverseExtension.isOpen_neighborhood.mem_nhds inverseExtension.mem_neighborhood)
  have hderivative : ContDiffAt ℝ (s - 1 : ℕ) derivativeExtension.extension p.1 :=
    derivativeExtension.contDiffOn_extension.contDiffAt
      (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood)
  have hvalue : derivativeExtension.extension p.1 =
      (system.derivativeEquiv
        ⟨system.diffeomorphism.inverse p.1, system.diffeomorphism.inverse_mapsTo hp.1⟩ :
          E →L[ℝ] E) :=
    (derivativeExtension.agrees ⟨hp.1, derivativeExtension.mem_neighborhood⟩).trans
      (system.mapDerivativeOnAmbient_eq_derivativeEquiv
        ⟨system.diffeomorphism.inverse p.1, system.diffeomorphism.inverse_mapsTo hp.1⟩)
  refine ⟨transposeLiftFormula inverseExtension.extension derivativeExtension.extension,
    contDiffAt_transposeLiftFormula _ _ p.1 p.2
      (system.derivativeEquiv
        ⟨system.diffeomorphism.inverse p.1, system.diffeomorphism.inverse_mapsTo hp.1⟩)
      hinverse hderivative hvalue hp.2, ?_⟩
  filter_upwards
    [continuous_fst.continuousAt.preimage_mem_nhds
      (inverseExtension.isOpen_neighborhood.mem_nhds inverseExtension.mem_neighborhood),
     continuous_fst.continuousAt.preimage_mem_nhds
      (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood)]
    with q hqInverse hqDerivative
  intro hq
  have hinverseValue := inverseExtension.agrees ⟨hq.1, hqInverse⟩
  have hderivativeValue := derivativeExtension.agrees ⟨hq.1, hqDerivative⟩
  simp only [transposeLiftFormula, SetValuedSystem.linearLiftInverseOnAmbient,
    hinverseValue, hderivativeValue]

end BoundedUncertainty
