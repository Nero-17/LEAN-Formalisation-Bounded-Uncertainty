import BoundedUncertainty.SecantCone
import Mathlib.Topology.Sequences

/-! Conversion of a two-moving-sequence secant criterion to a local filter
criterion. The diagonal quotient is zero, as usual for Lean's real division. -/

namespace BoundedUncertainty

open Set Topology Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Sequential normal flatness implies the uniform local two-point condition. -/
theorem isLittleO_chord_of_sequential_normalized_secants
    (subset : Set E) (point : E) (hpoint : point ∈ subset) (normal : E →L[ℝ] ℝ)
    (hsequences : ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |normal (second index - first index)| /
        ‖second index - first index‖) atTop (𝓝 0)) :
    (fun pair : E × E => normal (pair.2 - pair.1))
      =o[𝓝[subset ×ˢ subset] (point, point)] (fun pair => pair.2 - pair.1) := by
  classical
  rw [← isLittleO_norm_left, ← isLittleO_norm_right]
  apply (isLittleO_iff_tendsto (fun pair hzero => by
    rw [norm_eq_zero.mp hzero, map_zero, norm_zero])).mpr
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro sequence hsequence
  have heventual : ∀ᶠ index in atTop, sequence index ∈ subset ×ˢ subset :=
    hsequence.eventually self_mem_nhdsWithin
  let first : ℕ → E := fun index =>
    if sequence index ∈ subset ×ˢ subset then (sequence index).1 else point
  let second : ℕ → E := fun index =>
    if sequence index ∈ subset ×ˢ subset then (sequence index).2 else point
  have hfirstEq : first =ᶠ[atTop] (fun index => (sequence index).1) := by
    filter_upwards [heventual] with index hindex
    simp only [first, if_pos hindex]
  have hsecondEq : second =ᶠ[atTop] (fun index => (sequence index).2) := by
    filter_upwards [heventual] with index hindex
    simp only [second, if_pos hindex]
  have hfirstMem : ∀ index, first index ∈ subset := by
    intro index
    dsimp [first]
    split_ifs with hindex
    · exact hindex.1
    · exact hpoint
  have hsecondMem : ∀ index, second index ∈ subset := by
    intro index
    dsimp [second]
    split_ifs with hindex
    · exact hindex.2
    · exact hpoint
  have hambient := tendsto_nhds_of_tendsto_nhdsWithin hsequence
  have hfirst : Tendsto first atTop (𝓝 point) :=
    (continuous_fst.tendsto (point, point) |>.comp hambient).congr' hfirstEq.symm
  have hsecond : Tendsto second atTop (𝓝 point) :=
    (continuous_snd.tendsto (point, point) |>.comp hambient).congr' hsecondEq.symm
  apply (hsequences first second hfirstMem hsecondMem hfirst hsecond).congr'
  filter_upwards [hfirstEq, hsecondEq] with index hfirstIndex hsecondIndex
  simp only [Function.comp_apply, hfirstIndex, hsecondIndex, Real.norm_eq_abs]

end BoundedUncertainty
