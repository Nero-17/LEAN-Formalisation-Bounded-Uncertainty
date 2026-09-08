import BoundedUncertainty.BoundaryContributors
import Mathlib.Tactic.Module

/-!
Two-ball secant estimates for the converse direction of Theorem 4.9.
The geometric hypotheses are radial positions and exclusion from the interiors
of the constituent balls. A separate wrapper derives exclusion from actual
inflation-frontier membership.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Expanding the squared distance to a tangent ball gives a one-sided chord bound. -/
theorem inner_chord_ge_of_ball_exclusion
    (center z w normal : E) (radius : ℝ) (hpositive : 0 < radius)
    (hunit : ‖normal‖ = 1) (hposition : z = center + radius • normal)
    (hexclusion : radius ≤ ‖w - center‖) :
    -(‖w - z‖ ^ 2 / (2 * radius)) ≤ inner ℝ normal (w - z) := by
  have hdecomposition : w - center = (w - z) + radius • normal := by
    rw [hposition]
    module
  have hsquare : radius ^ 2 ≤ ‖w - center‖ ^ 2 := by
    nlinarith [norm_nonneg (w - center)]
  rw [hdecomposition, norm_add_sq_real, norm_smul, Real.norm_of_nonneg hpositive.le,
    hunit, mul_one, inner_smul_right, real_inner_comm normal (w - z)] at hsquare
  rw [← neg_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 * radius)).mpr
  nlinarith

/-- The ball at the other endpoint gives the opposite chord bound. -/
theorem inner_chord_le_of_ball_exclusion
    (center z w normal : E) (radius : ℝ) (hpositive : 0 < radius)
    (hunit : ‖normal‖ = 1) (hposition : w = center + radius • normal)
    (hexclusion : radius ≤ ‖z - center‖) :
    inner ℝ normal (w - z) ≤ ‖w - z‖ ^ 2 / (2 * radius) := by
  have hbound := inner_chord_ge_of_ball_exclusion center w z normal radius
    hpositive hunit hposition hexclusion
  rw [norm_sub_rev, inner_sub_right] at hbound
  rw [inner_sub_right]
  linarith

/-- Both endpoint normals may be compared with any fixed reference normal. -/
theorem normalized_secant_bounds_of_two_balls
    (firstCenter secondCenter z w firstNormal secondNormal referenceNormal : E)
    (firstRadius secondRadius : ℝ) (hfirstRadius : 0 < firstRadius)
    (hsecondRadius : 0 < secondRadius)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1)
    (hfirstPosition : z = firstCenter + firstRadius • firstNormal)
    (hsecondPosition : w = secondCenter + secondRadius • secondNormal)
    (hfirstExclusion : firstRadius ≤ ‖w - firstCenter‖)
    (hsecondExclusion : secondRadius ≤ ‖z - secondCenter‖) (hne : w ≠ z) :
    -‖w - z‖ / (2 * firstRadius) - ‖firstNormal - referenceNormal‖ ≤
        inner ℝ referenceNormal (w - z) / ‖w - z‖ ∧
      inner ℝ referenceNormal (w - z) / ‖w - z‖ ≤
        ‖w - z‖ / (2 * secondRadius) + ‖secondNormal - referenceNormal‖ := by
  have hchord : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlower := inner_chord_ge_of_ball_exclusion firstCenter z w firstNormal firstRadius
    hfirstRadius hfirstUnit hfirstPosition hfirstExclusion
  have hupper := inner_chord_le_of_ball_exclusion secondCenter z w secondNormal secondRadius
    hsecondRadius hsecondUnit hsecondPosition hsecondExclusion
  have hfirstError := abs_real_inner_le_norm (firstNormal - referenceNormal) (w - z)
  have hsecondError := abs_real_inner_le_norm (secondNormal - referenceNormal) (w - z)
  rw [inner_sub_left] at hfirstError hsecondError
  constructor
  · apply (le_div_iff₀ hchord).mpr
    have herror := (abs_le.mp hfirstError).2
    have harithmetic :
        (-‖w - z‖ / (2 * firstRadius) - ‖firstNormal - referenceNormal‖) * ‖w - z‖ =
          -(‖w - z‖ ^ 2 / (2 * firstRadius)) -
            ‖firstNormal - referenceNormal‖ * ‖w - z‖ := by ring
    rw [harithmetic]
    linarith
  · apply (div_le_iff₀ hchord).mpr
    have herror := (abs_le.mp hsecondError).1
    have harithmetic :
        (‖w - z‖ / (2 * secondRadius) + ‖secondNormal - referenceNormal‖) * ‖w - z‖ =
          ‖w - z‖ ^ 2 / (2 * secondRadius) +
            ‖secondNormal - referenceNormal‖ * ‖w - z‖ := by ring
    rw [harithmetic]
    linarith

/-- Actual contributing balls automatically satisfy the two exclusion inequalities. -/
theorem normalized_secant_bounds_of_frontier_inflation
    (radius : E → ℝ) (B : Set E)
    (firstCenter secondCenter z w firstNormal secondNormal referenceNormal : E)
    (hfirstCenter : firstCenter ∈ B) (hsecondCenter : secondCenter ∈ B)
    (hz : z ∈ frontier (inflation radius B)) (hw : w ∈ frontier (inflation radius B))
    (hfirstRadius : 0 < radius firstCenter) (hsecondRadius : 0 < radius secondCenter)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1)
    (hfirstPosition : z = firstCenter + radius firstCenter • firstNormal)
    (hsecondPosition : w = secondCenter + radius secondCenter • secondNormal) (hne : w ≠ z) :
    -‖w - z‖ / (2 * radius firstCenter) - ‖firstNormal - referenceNormal‖ ≤
        inner ℝ referenceNormal (w - z) / ‖w - z‖ ∧
      inner ℝ referenceNormal (w - z) / ‖w - z‖ ≤
        ‖w - z‖ / (2 * radius secondCenter) + ‖secondNormal - referenceNormal‖ := by
  apply normalized_secant_bounds_of_two_balls firstCenter secondCenter z w
    firstNormal secondNormal referenceNormal _ _ hfirstRadius hsecondRadius
    hfirstUnit hsecondUnit hfirstPosition hsecondPosition _ _ hne
  · simpa only [dist_eq_norm] using
      radius_le_dist_of_mem_frontier_inflation radius B w hw firstCenter hfirstCenter
  · simpa only [dist_eq_norm] using
      radius_le_dist_of_mem_frontier_inflation radius B z hz secondCenter hsecondCenter

/-- The ball estimates imply the secant limit whenever both chord/radius ratios vanish. -/
theorem tendsto_normalized_secant_of_two_balls
    (firstCenter secondCenter first second firstNormal secondNormal : ℕ → E)
    (firstRadius secondRadius : ℕ → ℝ) (referenceNormal : E)
    (hfirstRadius : ∀ᶠ k in atTop, 0 < firstRadius k)
    (hsecondRadius : ∀ᶠ k in atTop, 0 < secondRadius k)
    (hfirstUnit : ∀ k, ‖firstNormal k‖ = 1) (hsecondUnit : ∀ k, ‖secondNormal k‖ = 1)
    (hfirstPosition : ∀ k, first k = firstCenter k + firstRadius k • firstNormal k)
    (hsecondPosition : ∀ k, second k = secondCenter k + secondRadius k • secondNormal k)
    (hfirstExclusion : ∀ k, firstRadius k ≤ ‖second k - firstCenter k‖)
    (hsecondExclusion : ∀ k, secondRadius k ≤ ‖first k - secondCenter k‖)
    (hfirstRatio : Tendsto (fun k => ‖second k - first k‖ / firstRadius k) atTop (𝓝 0))
    (hsecondRatio : Tendsto (fun k => ‖second k - first k‖ / secondRadius k) atTop (𝓝 0))
    (hfirstNormal : Tendsto firstNormal atTop (𝓝 referenceNormal))
    (hsecondNormal : Tendsto secondNormal atTop (𝓝 referenceNormal)) :
    Tendsto (fun k => |inner ℝ referenceNormal (second k - first k)| /
      ‖second k - first k‖) atTop (𝓝 0) := by
  have hfirstQuotient : Tendsto
      (fun k => ‖second k - first k‖ / (2 * firstRadius k)) atTop (𝓝 0) := by
    simpa only [div_div, mul_comm, zero_div] using hfirstRatio.div_const 2
  have hsecondQuotient : Tendsto
      (fun k => ‖second k - first k‖ / (2 * secondRadius k)) atTop (𝓝 0) := by
    simpa only [div_div, mul_comm, zero_div] using hsecondRatio.div_const 2
  have hfirstError : Tendsto (fun k => ‖firstNormal k - referenceNormal‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hfirstNormal.sub (tendsto_const_nhds (x := referenceNormal))).norm
  have hsecondError : Tendsto (fun k => ‖secondNormal k - referenceNormal‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hsecondNormal.sub (tendsto_const_nhds (x := referenceNormal))).norm
  have hbounds : ∀ᶠ k in atTop,
      -‖second k - first k‖ / (2 * firstRadius k) - ‖firstNormal k - referenceNormal‖ ≤
        inner ℝ referenceNormal (second k - first k) / ‖second k - first k‖ ∧
      inner ℝ referenceNormal (second k - first k) / ‖second k - first k‖ ≤
        ‖second k - first k‖ / (2 * secondRadius k) + ‖secondNormal k - referenceNormal‖ := by
    filter_upwards [hfirstRadius, hsecondRadius] with k hkfirst hksecond
    by_cases heq : second k = first k
    · simp only [heq, sub_self, norm_zero, neg_zero, zero_div, zero_sub, inner_zero_right, zero_add]
      exact ⟨neg_nonpos.mpr (norm_nonneg _), norm_nonneg _⟩
    · exact normalized_secant_bounds_of_two_balls _ _ _ _ _ _ referenceNormal _ _
        hkfirst hksecond (hfirstUnit k) (hsecondUnit k) (hfirstPosition k) (hsecondPosition k)
        (hfirstExclusion k) (hsecondExclusion k) heq
  have hsigned : Tendsto (fun k => inner ℝ referenceNormal (second k - first k) /
      ‖second k - first k‖) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (show Tendsto (fun k => -‖second k - first k‖ / (2 * firstRadius k) -
        ‖firstNormal k - referenceNormal‖) atTop (𝓝 0) from by
        simpa only [neg_div, neg_zero, sub_zero] using hfirstQuotient.neg.sub hfirstError)
      (show Tendsto (fun k => ‖second k - first k‖ / (2 * secondRadius k) +
        ‖secondNormal k - referenceNormal‖) atTop (𝓝 0) from by
        simpa only [zero_add] using hsecondQuotient.add hsecondError)
      (hbounds.mono fun _ hk => hk.1) (hbounds.mono fun _ hk => hk.2)
  simpa only [abs_div, abs_norm, abs_zero] using hsigned.abs

/-- In particular, positive limiting radii and a continuous normal field give the required limit. -/
theorem tendsto_normalized_secant_of_positive_radius
    (radius : E → ℝ) (B : Set E)
    (firstCenter secondCenter first second firstNormal secondNormal : ℕ → E)
    (point referenceNormal : E) (limitingRadius : ℝ) (hpositive : 0 < limitingRadius)
    (hfirstCenter : ∀ k, firstCenter k ∈ B) (hsecondCenter : ∀ k, secondCenter k ∈ B)
    (hfirstFrontier : ∀ k, first k ∈ frontier (inflation radius B))
    (hsecondFrontier : ∀ k, second k ∈ frontier (inflation radius B))
    (hfirstUnit : ∀ k, ‖firstNormal k‖ = 1) (hsecondUnit : ∀ k, ‖secondNormal k‖ = 1)
    (hfirstPosition : ∀ k, first k = firstCenter k + radius (firstCenter k) • firstNormal k)
    (hsecondPosition : ∀ k, second k = secondCenter k + radius (secondCenter k) • secondNormal k)
    (hfirst : Tendsto first atTop (𝓝 point)) (hsecond : Tendsto second atTop (𝓝 point))
    (hfirstRadius : Tendsto (fun k => radius (firstCenter k)) atTop (𝓝 limitingRadius))
    (hsecondRadius : Tendsto (fun k => radius (secondCenter k)) atTop (𝓝 limitingRadius))
    (hfirstNormal : Tendsto firstNormal atTop (𝓝 referenceNormal))
    (hsecondNormal : Tendsto secondNormal atTop (𝓝 referenceNormal)) :
    Tendsto (fun k => |inner ℝ referenceNormal (second k - first k)| /
      ‖second k - first k‖) atTop (𝓝 0) := by
  have hchord : Tendsto (fun k => ‖second k - first k‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hsecond.sub hfirst).norm
  apply tendsto_normalized_secant_of_two_balls firstCenter secondCenter first second
    firstNormal secondNormal (fun k => radius (firstCenter k))
    (fun k => radius (secondCenter k)) referenceNormal
    (hfirstRadius.eventually (Ioi_mem_nhds hpositive))
    (hsecondRadius.eventually (Ioi_mem_nhds hpositive)) hfirstUnit hsecondUnit
    hfirstPosition hsecondPosition _ _ _ _ hfirstNormal hsecondNormal
  · intro k
    simpa only [dist_eq_norm] using radius_le_dist_of_mem_frontier_inflation
      radius B (second k) (hsecondFrontier k) (firstCenter k) (hfirstCenter k)
  · intro k
    simpa only [dist_eq_norm] using radius_le_dist_of_mem_frontier_inflation
      radius B (first k) (hfirstFrontier k) (secondCenter k) (hsecondCenter k)
  · simpa only [zero_div] using hchord.div hfirstRadius (ne_of_gt hpositive)
  · simpa only [zero_div] using hchord.div hsecondRadius (ne_of_gt hpositive)

end BoundedUncertainty
