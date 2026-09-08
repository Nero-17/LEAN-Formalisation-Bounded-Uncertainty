import BoundedUncertainty.SequentialSecants
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! The distinct-endpoint sequence hypothesis in Lemma 4.8 yields a uniform
two-point estimate, including diagonal pairs. No manifold or projection
openness is assumed or concluded by this analytical conversion. -/

namespace BoundedUncertainty

open Set Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_chord_bound_of_distinct_secants
    (subset : Set E) (point : E) (normal : E →L[ℝ] ℝ)
    (hsequences : ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |normal (second index - first index)| /
        ‖second index - first index‖) atTop (𝓝 0))
    (error : ℝ) (herror : 0 < error) :
    ∃ radius > 0, ∀ first ∈ subset, ∀ second ∈ subset,
      dist first point < radius → dist second point < radius →
        |normal (second - first)| ≤ error * ‖second - first‖ := by
  classical
  by_contra hnot
  push_neg at hnot
  have hbad : ∀ index : ℕ, ∃ first ∈ subset, ∃ second ∈ subset,
      dist first point < 1 / ((index : ℝ) + 1) ∧
      dist second point < 1 / ((index : ℝ) + 1) ∧
      error * ‖second - first‖ < |normal (second - first)| :=
    fun index => hnot (1 / ((index : ℝ) + 1)) (by positivity)
  choose first hfirstMem second hsecondMem hfirstNear hsecondNear hbound using hbad
  have hdistinct : ∀ index, first index ≠ second index := by
    intro index hequal
    have h := hbound index
    simp [hequal] at h
  have hfirst : Tendsto first atTop (𝓝 point) := by
    apply Metric.tendsto_atTop.mpr
    intro radius hradius
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hradius))
    exact ⟨N, fun index hindex => (hfirstNear index).trans (hN index hindex)⟩
  have hsecond : Tendsto second atTop (𝓝 point) := by
    apply Metric.tendsto_atTop.mpr
    intro radius hradius
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hradius))
    exact ⟨N, fun index hindex => (hsecondNear index).trans (hN index hindex)⟩
  have hlimit := hsequences first second hfirstMem hsecondMem hdistinct hfirst hsecond
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlimit.eventually (Iio_mem_nhds herror))
  have hnorm : 0 < ‖second N - first N‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (hdistinct N).symm)
  have hsmall := (div_lt_iff₀ hnorm).mp (hN N le_rfl)
  exact (not_lt_of_ge hsmall.le) (hbound N)

theorem isLittleO_chord_of_distinct_normalized_secants
    (subset : Set E) (point : E) (normal : E →L[ℝ] ℝ)
    (hsequences : ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |normal (second index - first index)| /
        ‖second index - first index‖) atTop (𝓝 0)) :
    (fun pair : E × E => normal (pair.2 - pair.1))
      =o[𝓝[subset ×ˢ subset] (point, point)] (fun pair => pair.2 - pair.1) := by
  apply IsLittleO.of_bound
  intro error herror
  obtain ⟨radius, hradius, hbound⟩ :=
    exists_uniform_chord_bound_of_distinct_secants subset point normal hsequences error herror
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨radius, hradius, ?_⟩
  intro pair hpair
  have hnear : dist pair.1 point < radius ∧ dist pair.2 point < radius := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using hpair.1
  simpa only [Real.norm_eq_abs] using
    hbound pair.1 hpair.2.1 pair.2 hpair.2.2 hnear.1 hnear.2

/-- The first geometric step of 4.8: orthogonal projection is locally injective.
This theorem does not assert that the projection image is open. -/
theorem exists_injOn_orthogonalProjection_of_distinct_secants
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (subset : Set E) (point normal : E) (hunit : ‖normal‖ = 1)
    (hsequences : ∀ first second : ℕ → E,
      (∀ index, first index ∈ subset) → (∀ index, second index ∈ subset) →
      (∀ index, first index ≠ second index) →
      Tendsto first atTop (𝓝 point) → Tendsto second atTop (𝓝 point) →
      Tendsto (fun index => |inner ℝ normal (second index - first index)| /
        ‖second index - first index‖) atTop (𝓝 0)) :
    ∃ radius > 0, InjOn (fun value : E => value - inner ℝ normal value • normal)
      (subset ∩ Metric.ball point radius) := by
  obtain ⟨radius, hradius, hbound⟩ :=
    exists_uniform_chord_bound_of_distinct_secants subset point (innerSL ℝ normal)
      hsequences (1 / 2) (by norm_num)
  refine ⟨radius, hradius, ?_⟩
  intro first hfirst second hsecond hequal
  have hsmall := hbound first hfirst.1 second hsecond.1 hfirst.2 hsecond.2
  have hparallel : second - first =
      inner ℝ normal (second - first) • normal := by
    rw [inner_sub_right, sub_smul]
    exact sub_eq_sub_iff_sub_eq_sub.mp hequal.symm
  have hnorm : ‖second - first‖ = |inner ℝ normal (second - first)| := by
    conv_lhs => rw [hparallel]
    rw [norm_smul, Real.norm_eq_abs, hunit, mul_one]
  have hzero : ‖second - first‖ = 0 := by
    change |inner ℝ normal (second - first)| ≤ 1 / 2 * ‖second - first‖ at hsmall
    rw [← hnorm] at hsmall
    nlinarith [norm_nonneg (second - first)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

end BoundedUncertainty
