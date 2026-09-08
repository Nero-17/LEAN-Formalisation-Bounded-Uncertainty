import BoundedUncertainty.MaximizerGeometry
import BoundedUncertainty.ForwardNormalBundle

/-! Continuity of the outward normal derived from pointwise C1 boundary data. -/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A local defining function vanishes at every nearby boundary point belonging to the set. -/
theorem C1BoundaryAt.defining_eq_zero_of_mem_frontier
    {A : Set E} {x z : E} (boundary : C1BoundaryAt A x)
    (hz : z ∈ frontier A) (hzA : z ∈ A) (hzU : z ∈ boundary.neighborhood) :
    boundary.defining z = 0 := by
  apply le_antisymm ((boundary.mem_iff z hzU).mp hzA)
  apply le_of_not_gt
  intro hnegative
  have hcontinuous := (boundary.contDiffOn_defining.continuousOn z hzU).continuousAt
    (boundary.isOpen_neighborhood.mem_nhds hzU)
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ boundary.neighborhood ∧ boundary.defining w < 0 :=
    inter_mem (boundary.isOpen_neighborhood.mem_nhds hzU)
      (hcontinuous.eventually_lt continuousAt_const hnegative)
  exact hz.2 (mem_interior_iff_mem_nhds.mpr
    (hnear.mono fun w hw => (boundary.mem_iff w hw.1).mpr hw.2.le))

/-- All chart choices give the same continuous normal field; continuity is not an input. -/
theorem continuous_boundaryNormal {A : Set E}
    (boundary : (x : frontier A) → C1BoundaryAt A x) :
    Continuous (fun x => (boundary x).normal) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hgradientContinuous : ContinuousAt (gradient (boundary x).defining) (x : E) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp
      (((boundary x).contDiffOn_defining.continuousOn_fderiv_of_isOpen
        (boundary x).isOpen_neighborhood (by norm_num)).continuousAt
        ((boundary x).isOpen_neighborhood.mem_nhds (boundary x).mem_neighborhood))
  have hnonzero : gradient (boundary x).defining (x : E) ≠ 0 := by
    rw [(boundary x).hasGradientAt_defining.gradient]
    exact norm_ne_zero_iff.mp ((boundary x).normal_unit.trans_ne one_ne_zero)
  have hnormalized : ContinuousAt
      (fun z : E => ‖gradient (boundary x).defining z‖⁻¹ • gradient (boundary x).defining z) x :=
    (hgradientContinuous.norm.inv₀ (norm_ne_zero_iff.mpr hnonzero)).smul hgradientContinuous
  apply (hnormalized.comp continuous_subtype_val.continuousAt).congr
  have hnonzeroNear : ∀ᶠ z in 𝓝 (x : E), gradient (boundary x).defining z ≠ 0 :=
    hgradientContinuous.eventually_ne hnonzero
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    ((boundary x).isOpen_neighborhood.mem_nhds (boundary x).mem_neighborhood),
    continuous_subtype_val.continuousAt.preimage_mem_nhds hnonzeroNear] with z hzU hzNonzero
  have hzero := (boundary x).defining_eq_zero_of_mem_frontier z.property (boundary z).mem hzU
  have hmax : IsLocalMaxOn (boundary x).defining A (z : E) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      ((boundary x).isOpen_neighborhood.mem_nhds hzU)] with w hwA hwU
    rw [hzero]
    exact ((boundary x).mem_iff w hwU).mp hwA
  have hgradient := (boundary x).contDiffOn_defining.differentiableOn_one.hasGradientAt
    ((boundary x).isOpen_neighborhood.mem_nhds hzU)
  exact (boundary z).normal_eq_normalized_gradient_of_isLocalMaxOn
    (boundary x).defining (gradient (boundary x).defining z) hgradient hzNonzero hmax

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuous_outwardNormal {A : Set E} (hregular : IsRegularClosed A)
    (charts : (x : frontier A) → C1FrontierGraphAt (F := F) A x) :
    Continuous (fun x => (charts x).outwardNormal hregular) :=
  continuous_boundaryNormal (fun x => (charts x).toC1BoundaryAt hregular)

theorem continuous_outwardNormalPair {A : Set E} (hregular : IsRegularClosed A)
    (charts : (x : frontier A) → C1FrontierGraphAt (F := F) A x) :
    Continuous (outwardNormalPair A hregular charts) :=
  continuous_subtype_val.prodMk (continuous_outwardNormal hregular charts)

variable {r s : ℕ}

/-- The raw projected formula is defined before any smoothness of the recipient boundary. -/
noncomputable def SetValuedSystem.boundaryProjection
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (boundary : (x : frontier A) → C1BoundaryAt A x) : frontier A → E :=
  fun x => (system.boundaryFormula (system.boundaryNormalInput A hA boundary x)).1

theorem SetValuedSystem.continuous_boundaryProjection
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain)
    (boundary : (x : frontier A) → C1BoundaryAt A x) :
    Continuous (system.boundaryProjection A hA boundary) := by
  have hinput : Continuous (system.boundaryNormalInput A hA boundary) :=
    (continuous_subtype_val.subtype_mk _).prodMk
      ((continuous_boundaryNormal boundary).subtype_mk _)
  exact continuous_fst.comp ((system.isEmbedding_boundaryFormula hcontraction).continuous.comp hinput)

end BoundedUncertainty
