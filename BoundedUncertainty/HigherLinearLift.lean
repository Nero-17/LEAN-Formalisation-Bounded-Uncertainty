import BoundedUncertainty.LocalExtensionOperations
import BoundedUncertainty.HigherExponential
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Higher regularity of the actual linear lift

The raw ambient formula uses the canonical derivative representative, ring
inversion, the real adjoint, and normalization. Inversion is differentiated
only at an invertible operator, and the norm only at a nonzero output vector.
Neither restriction is assumed away: both follow from the actual derivative
equivalence and the unit input normal.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- An ambient formula for the linear lift, with its differential represented
as an operator field. Values outside the stated source bundle are auxiliary. -/
noncomputable def linearLiftFormula (f : E → E) (D : E → E →L[ℝ] E) (p : E × E) : E × E :=
  (f p.1,
    ‖ContinuousLinearMap.adjoint (Ring.inverse (D p.1)) p.2‖⁻¹ •
      ContinuousLinearMap.adjoint (Ring.inverse (D p.1)) p.2)

/-- The inverse-transpose formula is locally smooth at a genuine invertible
differential and a unit normal. This lemma has no contraction hypothesis. -/
theorem contDiffAt_linearLiftFormula {order : WithTop ℕ∞}
    (f : E → E) (D : E → E →L[ℝ] E) (x n : E) (T : E ≃L[ℝ] E)
    (hf : ContDiffAt ℝ order f x) (hD : ContDiffAt ℝ order D x)
    (hvalue : D x = (T : E →L[ℝ] E)) (hn : ‖n‖ = 1) :
    ContDiffAt ℝ order (linearLiftFormula f D) (x, n) := by
  have hinverse : ContDiffAt ℝ order Ring.inverse (D x) := by
    rw [hvalue]
    exact contDiffAt_ringInverse ℝ T.toUnit
  have hoperator : ContDiffAt ℝ order
      (fun p : E × E => ContinuousLinearMap.adjoint (Ring.inverse (D p.1))) (x, n) :=
    ContinuousLinearMap.adjoint.contDiff.contDiffAt.comp (x, n)
      (hinverse.comp (x, n) (hD.comp (x, n) contDiffAt_fst))
  have hvector : ContDiffAt ℝ order
      (fun p : E × E => ContinuousLinearMap.adjoint (Ring.inverse (D p.1)) p.2) (x, n) :=
    hoperator.clm_apply contDiffAt_snd
  have hnonzero : ContinuousLinearMap.adjoint (Ring.inverse (D x)) n ≠ 0 := by
    rw [hvalue, ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]
    exact linearMap_unit_ne_zero (inverseTranspose T) hn
  exact (hf.comp (x, n) contDiffAt_fst).prodMk
    (((hvector.norm ℝ hnonzero).inv (norm_ne_zero_iff.mpr hnonzero)).smul hvector)

variable {r s : ℕ}

/-- The true linear lift as an ambient representative, before any contraction
assumption on the separate radius function. -/
noncomputable def SetValuedSystem.linearLiftOnAmbient
    (system : SetValuedSystem (E := E) r s) : E × E → E × E :=
  linearLiftFormula system.map system.mapDerivativeOnAmbient

/-- Restriction to the source bundle agrees exactly with the existing typed lift. -/
theorem SetValuedSystem.linearLiftOnAmbient_apply
    (system : SetValuedSystem (E := E) r s)
    (p : system.domain × {n : E // ‖n‖ = 1}) :
    system.linearLiftOnAmbient ((p.1 : E), (p.2 : E)) =
      (((system.linearLift p).1 : E), ((system.linearLift p).2 : E)) := by
  unfold SetValuedSystem.linearLiftOnAmbient linearLiftFormula
  rw [system.mapDerivativeOnAmbient_eq_derivativeEquiv p.1,
    ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]
  rfl

/-- The actual linear lift has local `C^(s-1)` ambient extensions on its source bundle. -/
theorem SetValuedSystem.hasLocalExtensionOn_linearLiftOnAmbient
    (system : SetValuedSystem (E := E) r s) :
    HasLocalExtensionOn (s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
      system.linearLiftOnAmbient := by
  apply hasLocalExtensionOn_of_locally_contDiffAt
  intro p hp
  obtain ⟨mapExtension⟩ := system.diffeomorphism.forward_extension p.1 hp.1
  obtain ⟨derivativeExtension⟩ := system.hasLocalExtensionOn_mapDerivativeOnAmbient p.1 hp.1
  have hmap : ContDiffAt ℝ (s - 1 : ℕ) mapExtension.extension p.1 :=
    (mapExtension.contDiffOn_extension.of_le (by exact_mod_cast Nat.sub_le s 1)).contDiffAt
      (mapExtension.isOpen_neighborhood.mem_nhds mapExtension.mem_neighborhood)
  have hderivative : ContDiffAt ℝ (s - 1 : ℕ) derivativeExtension.extension p.1 :=
    derivativeExtension.contDiffOn_extension.contDiffAt
      (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood)
  have hvalue : derivativeExtension.extension p.1 =
      (system.derivativeEquiv ⟨p.1, hp.1⟩ : E →L[ℝ] E) :=
    (derivativeExtension.agrees ⟨hp.1, derivativeExtension.mem_neighborhood⟩).trans
      (system.mapDerivativeOnAmbient_eq_derivativeEquiv ⟨p.1, hp.1⟩)
  refine ⟨linearLiftFormula mapExtension.extension derivativeExtension.extension,
    contDiffAt_linearLiftFormula _ _ p.1 p.2 (system.derivativeEquiv ⟨p.1, hp.1⟩)
      hmap hderivative hvalue hp.2, ?_⟩
  filter_upwards
    [continuous_fst.continuousAt.preimage_mem_nhds
      (mapExtension.isOpen_neighborhood.mem_nhds mapExtension.mem_neighborhood),
     continuous_fst.continuousAt.preimage_mem_nhds
      (derivativeExtension.isOpen_neighborhood.mem_nhds derivativeExtension.mem_neighborhood)]
    with q hqMap hqDerivative
  intro hq
  have hmapValue := mapExtension.agrees ⟨hq.1, hqMap⟩
  have hderivativeValue := derivativeExtension.agrees ⟨hq.1, hqDerivative⟩
  simp only [linearLiftFormula, SetValuedSystem.linearLiftOnAmbient, hmapValue, hderivativeValue]

/-- The ambient representative sends domain points and unit normals to the
same bundle, as required for composition with the exponential formula. -/
theorem SetValuedSystem.linearLiftOnAmbient_mapsTo
    (system : SetValuedSystem (E := E) r s) :
    Set.MapsTo system.linearLiftOnAmbient (system.domain ×ˢ {n : E | ‖n‖ = 1})
      (system.domain ×ˢ {n : E | ‖n‖ = 1}) := by
  intro p hp
  rw [system.linearLiftOnAmbient_apply (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)]
  exact ⟨(system.linearLift (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)).1.property,
    (system.linearLift (⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩)).2.property⟩

end BoundedUncertainty
