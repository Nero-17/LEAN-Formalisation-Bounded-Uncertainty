import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
Local restrictions of ambient homeomorphisms to arbitrary subspaces. Neither
subspace is assumed open: the chart source and target are relatively open.
-/

namespace BoundedUncertainty

open Set Topology

variable {E H : Type*} [TopologicalSpace E] [TopologicalSpace H]

/-- An ambient homeomorphism that identifies two sets on an open neighbourhood
induces an open partial homeomorphism of their actual subtypes. -/
noncomputable def relativeOpenPartialHomeomorph (coordinates : E ≃ₜ H)
    (B : Set E) (C : Set H) (U : Set E) (hU : IsOpen U)
    (hsets : ∀ z ∈ U, z ∈ B ↔ coordinates z ∈ C)
    (y : E) (hyB : y ∈ B) (hyU : y ∈ U) : OpenPartialHomeomorph B C := by
  classical
  let forward : B → C := fun z =>
    if hz : coordinates z ∈ C then ⟨coordinates z, hz⟩
    else ⟨coordinates y, (hsets y hyU).mp hyB⟩
  let backward : C → B := fun z =>
    if hz : coordinates.symm z ∈ B then ⟨coordinates.symm z, hz⟩ else ⟨y, hyB⟩
  have hforward (z : B) (hz : (z : E) ∈ U) :
      (forward z : H) = coordinates z := by
    simp only [forward, dif_pos ((hsets z hz).mp z.property)]
  have hbackward (z : C) (hz : coordinates.symm z ∈ U) :
      (backward z : E) = coordinates.symm z := by
    have hmem : coordinates.symm z ∈ B :=
      (hsets _ hz).mpr (by simp only [coordinates.apply_symm_apply, z.property])
    simp only [backward, dif_pos hmem]
  exact {
    toFun := forward
    invFun := backward
    source := Subtype.val ⁻¹' U
    target := (fun z : C => coordinates.symm z) ⁻¹' U
    map_source' := by
      intro z hz
      change coordinates.symm (forward z) ∈ U
      rw [hforward z hz, coordinates.symm_apply_apply]
      exact hz
    map_target' := by
      intro z hz
      change (backward z : E) ∈ U
      rw [hbackward z hz]
      exact hz
    left_inv' := by
      intro z hz
      apply Subtype.ext
      rw [hbackward _ (by rw [hforward z hz, coordinates.symm_apply_apply]; exact hz)]
      rw [hforward z hz, coordinates.symm_apply_apply]
    right_inv' := by
      intro z hz
      apply Subtype.ext
      rw [hforward _ (by rw [hbackward z hz]; exact hz)]
      rw [hbackward z hz, coordinates.apply_symm_apply]
    open_source := hU.preimage continuous_subtype_val
    open_target := hU.preimage (coordinates.symm.continuous.comp continuous_subtype_val)
    continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      ((coordinates.continuous.comp continuous_subtype_val).continuousOn.congr
        (fun z hz => hforward z hz))
    continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      ((coordinates.symm.continuous.comp continuous_subtype_val).continuousOn.congr
        (fun z hz => hbackward z hz)) }

@[simp] theorem relativeOpenPartialHomeomorph_source (coordinates : E ≃ₜ H)
    (B : Set E) (C : Set H) (U : Set E) (hU : IsOpen U)
    (hsets : ∀ z ∈ U, z ∈ B ↔ coordinates z ∈ C)
    (y : E) (hyB : y ∈ B) (hyU : y ∈ U) :
    (relativeOpenPartialHomeomorph coordinates B C U hU hsets y hyB hyU).source =
      Subtype.val ⁻¹' U := rfl

@[simp] theorem relativeOpenPartialHomeomorph_target (coordinates : E ≃ₜ H)
    (B : Set E) (C : Set H) (U : Set E) (hU : IsOpen U)
    (hsets : ∀ z ∈ U, z ∈ B ↔ coordinates z ∈ C)
    (y : E) (hyB : y ∈ B) (hyU : y ∈ U) :
    (relativeOpenPartialHomeomorph coordinates B C U hU hsets y hyB hyU).target =
      (fun z : C => coordinates.symm z) ⁻¹' U := rfl

end BoundedUncertainty
