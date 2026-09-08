import BoundedUncertainty.FrontierNormalCriterion
import BoundedUncertainty.SequentialSecants

/-! The actual-frontier C1 criterion in a unit-normal and sequential interface.
This is the interface used for the converse direction of Theorem 4.9. -/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Continuous unit normals with vanishing two-moving-point secants give actual
C1 frontier charts of a regular closed set. Diagonal quotients are zero. -/
theorem nonempty_c1FrontierGraphAt_of_sequential_normal_secants {B : Set E}
    (hB : IsRegularClosed B) (normal : frontier B → E) (hcontinuous : Continuous normal)
    (hunit : ∀ point, ‖normal point‖ = 1)
    (hsecants : ∀ point : frontier B, ∀ first second : ℕ → frontier B,
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |inner ℝ (normal point)
        ((second index : E) - (first index : E))| /
          ‖(second index : E) - (first index : E)‖) atTop (𝓝 0))
    (point : frontier B) :
    Nonempty (C1FrontierGraphAt (F := (InnerProductSpace.toDual ℝ E (normal point)).ker)
      B point) := by
  classical
  let covector : E → E →L[ℝ] ℝ := fun value =>
    if hvalue : value ∈ frontier B then InnerProductSpace.toDual ℝ E (normal ⟨value, hvalue⟩)
      else 0
  have hcovector (value : frontier B) : covector value =
      InnerProductSpace.toDual ℝ E (normal value) := by
    simp only [covector, dif_pos value.property]
  have hcovectorContinuous : ContinuousOn covector (frontier B) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun value : frontier B => covector value)
    have h := (InnerProductSpace.toDual ℝ E).continuous.comp hcontinuous
    exact h.congr (fun value => (hcovector value).symm)
  have hcovectorSecants : ∀ value ∈ frontier B,
      (fun pair : E × E => covector value (pair.2 - pair.1))
        =o[𝓝[frontier B ×ˢ frontier B] (value, value)] (fun pair => pair.2 - pair.1) := by
    intro value hvalue
    apply isLittleO_chord_of_sequential_normalized_secants (frontier B) value hvalue (covector value)
    intro first second hfirstMem hsecondMem hfirst hsecond
    have hfirstSubtype : Tendsto (fun index => (⟨first index, hfirstMem index⟩ : frontier B))
        atTop (𝓝 ⟨value, hvalue⟩) := tendsto_subtype_rng.mpr hfirst
    have hsecondSubtype : Tendsto (fun index => (⟨second index, hsecondMem index⟩ : frontier B))
        atTop (𝓝 ⟨value, hvalue⟩) := tendsto_subtype_rng.mpr hsecond
    simpa only [covector, dif_pos hvalue, InnerProductSpace.toDual_apply_apply] using
      hsecants ⟨value, hvalue⟩ _ _ hfirstSubtype hsecondSubtype
  have htransverse : covector point (normal point) = 1 := by
    rw [hcovector]
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq, hunit, one_pow]
  have h := nonempty_c1FrontierGraphAt_of_normal_chords hB covector hcovectorContinuous
    hcovectorSecants point point.property (normal point) htransverse
  rw [hcovector point] at h
  exact h

end BoundedUncertainty
