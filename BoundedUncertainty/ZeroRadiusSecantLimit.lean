import BoundedUncertainty.ZeroRadiusChordAlgebra
import BoundedUncertainty.ZeroRadiusSecants

/-!
A quantitative small/large-radius argument replaces the subsequence split in
Theorem 4.9. The source flatness estimates and normal continuity alone control
all recipient chords, including pairs with a zero constituent radius.
-/

namespace BoundedUncertainty

open Set Filter Topology Asymptotics

/-- Quantitative form of the two radius/chord regimes, with a uniform error bound. -/
theorem secant_error_le_of_small_source_errors
    (sourceDistance recipientDistance minimumRadius maximumRadius normalComponent error : ℝ)
    (hsourceDistance : 0 ≤ sourceDistance) (hrecipientDistance : 0 < recipientDistance)
    (hminimumRadius : 0 ≤ minimumRadius) (hradii : minimumRadius ≤ maximumRadius)
    (herror : 0 < error) (herrorSmall : error ≤ 1 / 8)
    (hsource : (1 - error ^ 2) * sourceDistance ≤
      recipientDistance + 2 * minimumRadius * error)
    (hnormal : normalComponent ≤ 2 * error ^ 2 * sourceDistance + maximumRadius * error ^ 2)
    (hradiusDifference : maximumRadius - minimumRadius ≤ error ^ 2 * sourceDistance)
    (hballs : 0 < minimumRadius →
      2 * minimumRadius * normalComponent ≤ recipientDistance ^ 2 +
        2 * minimumRadius * error * recipientDistance) :
    normalComponent ≤ 4 * error * recipientDistance := by
  have hmaximumRadius : 0 ≤ maximumRadius := hminimumRadius.trans hradii
  have hsquareHalf : error ^ 2 ≤ 1 / 2 := by nlinarith
  have hsquareQuarter : error ^ 2 ≤ 1 / 4 := by nlinarith
  have hsourceHalf := mul_le_mul_of_nonneg_right hsquareHalf hsourceDistance
  by_cases hsmall : error * maximumRadius ≤ recipientDistance
  · have hminimumScaled := mul_le_mul_of_nonneg_left hradii herror.le
    have hsourceBound : sourceDistance ≤ 6 * recipientDistance := by nlinarith
    have hsourceScaled := mul_le_mul_of_nonneg_left hsourceBound
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg error))
    have hradiusScaled := mul_le_mul_of_nonneg_right hsmall herror.le
    have hcoefficient : 12 * error ^ 2 + error ≤ 4 * error := by nlinarith
    have hfinal := mul_le_mul_of_nonneg_right hcoefficient hrecipientDistance.le
    nlinarith
  · have hlarge : recipientDistance < error * maximumRadius := lt_of_not_ge hsmall
    have hsourceBound : sourceDistance ≤ 2 * recipientDistance + 4 * minimumRadius * error := by
      nlinarith
    have hquarter := mul_le_mul_of_nonneg_right hsquareQuarter hsourceDistance
    have hminimumError := mul_le_mul_of_nonneg_right herrorSmall hminimumRadius
    have hmaximumError := mul_le_mul_of_nonneg_right herrorSmall hmaximumRadius
    have hcomparable : maximumRadius / 2 ≤ minimumRadius := by nlinarith
    have hmaximumPositive : 0 < maximumRadius := by nlinarith
    have hminimumPositive : 0 < minimumRadius := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hcomparable herror.le
    have hchordBound : recipientDistance ≤ 2 * minimumRadius * error := by nlinarith
    have hquadratic := mul_le_mul_of_nonneg_right hchordBound hrecipientDistance.le
    have hball := hballs hminimumPositive
    have hnormalBound : normalComponent ≤ 2 * error * recipientDistance := by nlinarith
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Small source and normal-field errors give a uniform recipient secant estimate. -/
theorem recipient_secant_le_of_small_source_errors
    (firstCenter secondCenter first second firstNormal secondNormal referenceNormal : E)
    (firstRadius secondRadius error : ℝ) (hfirstRadius : 0 ≤ firstRadius)
    (hsecondRadius : 0 ≤ secondRadius) (herror : 0 < error) (herrorSmall : error ≤ 1 / 8)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1)
    (hreferenceUnit : ‖referenceNormal‖ = 1)
    (hfirstPosition : first = firstCenter + firstRadius • firstNormal)
    (hsecondPosition : second = secondCenter + secondRadius • secondNormal)
    (hfirstExclusion : firstRadius ≤ ‖second - firstCenter‖)
    (hsecondExclusion : secondRadius ≤ ‖first - secondCenter‖)
    (hsourceNormal : |inner ℝ referenceNormal (secondCenter - firstCenter)| ≤
      error ^ 2 * ‖secondCenter - firstCenter‖)
    (hsourceRadius : |secondRadius - firstRadius| ≤ error ^ 2 * ‖secondCenter - firstCenter‖)
    (hfirstError : ‖firstNormal - referenceNormal‖ ≤ error)
    (hsecondError : ‖secondNormal - referenceNormal‖ ≤ error) :
    |inner ℝ referenceNormal (second - first)| ≤ 4 * error * ‖second - first‖ := by
  by_cases heq : second = first
  · simp only [heq, sub_self, inner_zero_right, abs_zero, norm_zero, mul_zero, le_refl]
  have hchord : 0 < ‖second - first‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have hmaximumError : max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖ ≤ error :=
    max_le hfirstError hsecondError
  have hminimumRadius : 0 ≤ min firstRadius secondRadius := le_min hfirstRadius hsecondRadius
  have hmaximumRadius : 0 ≤ max firstRadius secondRadius := hfirstRadius.trans (le_max_left _ _)
  apply secant_error_le_of_small_source_errors ‖secondCenter - firstCenter‖ ‖second - first‖
    (min firstRadius secondRadius) (max firstRadius secondRadius)
    |inner ℝ referenceNormal (second - first)| error (norm_nonneg _) hchord hminimumRadius
    (le_trans (min_le_left _ _) (le_max_left _ _)) herror herrorSmall
  · have hbound := source_chord_le_recipient_chord firstCenter secondCenter first second
      firstNormal secondNormal referenceNormal firstRadius secondRadius hfirstRadius hsecondRadius
      hfirstUnit hsecondUnit hfirstPosition hsecondPosition
    have hscaled := mul_le_mul_of_nonneg_left hmaximumError
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hminimumRadius)
    nlinarith
  · have hbound := abs_inner_recipient_chord_le firstCenter secondCenter first second
      firstNormal secondNormal referenceNormal firstRadius secondRadius hfirstRadius
      hfirstUnit hsecondUnit hreferenceUnit hfirstPosition hsecondPosition
    have hsquared :
        (max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖) ^ 2 ≤ error ^ 2 :=
      (sq_le_sq₀ ((norm_nonneg _).trans (le_max_left _ _)) herror.le).mpr hmaximumError
    have hscaled := mul_le_mul_of_nonneg_left hsquared hmaximumRadius
    nlinarith
  · rw [max_sub_min_eq_abs]
    exact hsourceRadius
  · intro hminimumPositive
    have hfirstPositive := lt_of_lt_of_le hminimumPositive (min_le_left firstRadius secondRadius)
    have hsecondPositive := lt_of_lt_of_le hminimumPositive (min_le_right firstRadius secondRadius)
    have hbounds := normalized_secant_bounds_of_two_balls firstCenter secondCenter first second
      firstNormal secondNormal referenceNormal firstRadius secondRadius
      hfirstPositive hsecondPositive hfirstUnit hsecondUnit hfirstPosition hsecondPosition
      hfirstExclusion hsecondExclusion heq
    have hdenominator : 0 < 2 * min firstRadius secondRadius := by positivity
    have hfirstQuotient := div_le_div_of_nonneg_left (norm_nonneg (second - first)) hdenominator
      (mul_le_mul_of_nonneg_left (min_le_left firstRadius secondRadius) (by norm_num : (0 : ℝ) ≤ 2))
    have hsecondQuotient := div_le_div_of_nonneg_left (norm_nonneg (second - first)) hdenominator
      (mul_le_mul_of_nonneg_left (min_le_right firstRadius secondRadius) (by norm_num : (0 : ℝ) ≤ 2))
    have hratio : |inner ℝ referenceNormal (second - first) / ‖second - first‖| ≤
        ‖second - first‖ / (2 * min firstRadius secondRadius) + error := by
      apply abs_le.mpr
      simp only [neg_div] at hbounds
      constructor <;> linarith [hbounds.1, hbounds.2]
    rw [abs_div, abs_norm] at hratio
    have hcomponent := (div_le_iff₀ hchord).mp hratio
    have hscaled := mul_le_mul_of_nonneg_left hcomponent hdenominator.le
    have hidentity : (2 * min firstRadius secondRadius) *
        ((‖second - first‖ / (2 * min firstRadius secondRadius) + error) * ‖second - first‖) =
        ‖second - first‖ ^ 2 + 2 * min firstRadius secondRadius * error * ‖second - first‖ := by
      field_simp [ne_of_gt hminimumPositive]
    rw [hidentity] at hscaled
    exact hscaled

/-- Two-moving-point source flatness and normal continuity control every recipient secant.
No distinctness assumption is needed: a diagonal quotient is zero. -/
theorem tendsto_normalized_secant_of_source_flatness
    (firstCenter secondCenter first second firstNormal secondNormal : ℕ → E)
    (firstRadius secondRadius : ℕ → ℝ) (referenceNormal : E)
    (hfirstRadius : ∀ k, 0 ≤ firstRadius k) (hsecondRadius : ∀ k, 0 ≤ secondRadius k)
    (hfirstUnit : ∀ k, ‖firstNormal k‖ = 1) (hsecondUnit : ∀ k, ‖secondNormal k‖ = 1)
    (hreferenceUnit : ‖referenceNormal‖ = 1)
    (hfirstPosition : ∀ k, first k = firstCenter k + firstRadius k • firstNormal k)
    (hsecondPosition : ∀ k, second k = secondCenter k + secondRadius k • secondNormal k)
    (hfirstExclusion : ∀ k, firstRadius k ≤ ‖second k - firstCenter k‖)
    (hsecondExclusion : ∀ k, secondRadius k ≤ ‖first k - secondCenter k‖)
    (hsourceNormal : (fun k => inner ℝ referenceNormal (secondCenter k - firstCenter k))
      =o[atTop] (fun k => secondCenter k - firstCenter k))
    (hsourceRadius : (fun k => secondRadius k - firstRadius k)
      =o[atTop] (fun k => secondCenter k - firstCenter k))
    (hfirstNormal : Tendsto firstNormal atTop (𝓝 referenceNormal))
    (hsecondNormal : Tendsto secondNormal atTop (𝓝 referenceNormal)) :
    Tendsto (fun k => |inner ℝ referenceNormal (second k - first k)| /
      ‖second k - first k‖) atTop (𝓝 0) := by
  have hfirstError : Tendsto (fun k => ‖firstNormal k - referenceNormal‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hfirstNormal.sub (tendsto_const_nhds (x := referenceNormal))).norm
  have hsecondError : Tendsto (fun k => ‖secondNormal k - referenceNormal‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hsecondNormal.sub (tendsto_const_nhds (x := referenceNormal))).norm
  apply Metric.tendsto_nhds.mpr
  intro tolerance htolerance
  have herror : 0 < min (tolerance / 8) (1 / 8 : ℝ) := by positivity
  have herrorSmall : min (tolerance / 8) (1 / 8 : ℝ) ≤ 1 / 8 := min_le_right _ _
  have herrorTolerance : 4 * min (tolerance / 8) (1 / 8 : ℝ) < tolerance := by
    have := min_le_left (tolerance / 8) (1 / 8 : ℝ)
    linarith
  filter_upwards [hsourceNormal.def (sq_pos_of_pos herror),
    hsourceRadius.def (sq_pos_of_pos herror),
    hfirstError.eventually (Iio_mem_nhds herror),
    hsecondError.eventually (Iio_mem_nhds herror)] with k hkNormal hkRadius hkFirst hkSecond
  simp only [Real.norm_eq_abs] at hkNormal hkRadius
  have hbound := recipient_secant_le_of_small_source_errors
    (firstCenter k) (secondCenter k) (first k) (second k)
    (firstNormal k) (secondNormal k) referenceNormal (firstRadius k) (secondRadius k)
    (min (tolerance / 8) (1 / 8 : ℝ)) (hfirstRadius k) (hsecondRadius k) herror herrorSmall
    (hfirstUnit k) (hsecondUnit k) hreferenceUnit (hfirstPosition k) (hsecondPosition k)
    (hfirstExclusion k) (hsecondExclusion k) hkNormal hkRadius hkFirst.le hkSecond.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (abs_nonneg _) (norm_nonneg _))]
  by_cases heq : second k = first k
  · simpa only [heq, sub_self, inner_zero_right, abs_zero, norm_zero, zero_div] using htolerance
  · exact ((div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr heq))).mpr hbound).trans_lt
      herrorTolerance

end BoundedUncertainty
