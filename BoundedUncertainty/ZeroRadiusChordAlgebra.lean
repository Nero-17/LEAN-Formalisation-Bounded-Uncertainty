import BoundedUncertainty.SecantEstimates

/-! Finite chord estimates used at zero-radius points in Theorem 4.9. -/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_radial_difference_le_with_firstRadius
    (firstNormal secondNormal : E) (firstRadius secondRadius : ℝ)
    (hfirst : 0 ≤ firstRadius)
    (hsecondUnit : ‖secondNormal‖ = 1) :
    ‖secondRadius • secondNormal - firstRadius • firstNormal‖ ≤
      |secondRadius - firstRadius| + firstRadius * ‖secondNormal - firstNormal‖ := by
  have hdecomposition : secondRadius • secondNormal - firstRadius • firstNormal =
      (secondRadius - firstRadius) • secondNormal + firstRadius • (secondNormal - firstNormal) := by
    module
  rw [hdecomposition]
  calc
    _ ≤ ‖(secondRadius - firstRadius) • secondNormal‖ +
        ‖firstRadius • (secondNormal - firstNormal)‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hfirst, hsecondUnit, mul_one]

theorem norm_radial_difference_le
    (firstNormal secondNormal : E) (firstRadius secondRadius : ℝ)
    (hfirst : 0 ≤ firstRadius) (hsecond : 0 ≤ secondRadius)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1) :
    ‖secondRadius • secondNormal - firstRadius • firstNormal‖ ≤
      |secondRadius - firstRadius| + min firstRadius secondRadius * ‖secondNormal - firstNormal‖ := by
  rcases le_total firstRadius secondRadius with hle | hle
  · simpa only [min_eq_left hle] using
      norm_radial_difference_le_with_firstRadius firstNormal secondNormal firstRadius secondRadius hfirst hsecondUnit
  · have hbound := norm_radial_difference_le_with_firstRadius secondNormal firstNormal
      secondRadius firstRadius hsecond hfirstUnit
    rw [norm_sub_rev, abs_sub_comm, norm_sub_rev firstNormal secondNormal] at hbound
    simpa only [min_eq_right hle] using hbound

/-- Rewriting with the smaller radius controls source separation by recipient separation. -/
theorem source_chord_le_recipient_chord
    (firstCenter secondCenter first second firstNormal secondNormal referenceNormal : E)
    (firstRadius secondRadius : ℝ) (hfirstRadius : 0 ≤ firstRadius)
    (hsecondRadius : 0 ≤ secondRadius)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1)
    (hfirstPosition : first = firstCenter + firstRadius • firstNormal)
    (hsecondPosition : second = secondCenter + secondRadius • secondNormal) :
    ‖secondCenter - firstCenter‖ ≤ ‖second - first‖ + |secondRadius - firstRadius| +
      2 * min firstRadius secondRadius *
        max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖ := by
  have hdecomposition : secondCenter - firstCenter = (second - first) -
      (secondRadius • secondNormal - firstRadius • firstNormal) := by
    rw [hfirstPosition, hsecondPosition]
    module
  have htriangle := norm_sub_le (second - first)
    (secondRadius • secondNormal - firstRadius • firstNormal)
  rw [← hdecomposition] at htriangle
  have hradial := norm_radial_difference_le firstNormal secondNormal firstRadius secondRadius
    hfirstRadius hsecondRadius hfirstUnit hsecondUnit
  have hnormal : ‖secondNormal - firstNormal‖ ≤
      2 * max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖ := by
    have hbound := norm_sub_le_norm_sub_add_norm_sub secondNormal referenceNormal firstNormal
    rw [norm_sub_rev referenceNormal firstNormal] at hbound
    linarith [le_max_left ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖,
      le_max_right ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖]
  have hscaled := mul_le_mul_of_nonneg_left hnormal (le_min hfirstRadius hsecondRadius)
  linarith

/-- Unit-vector geometry makes the normal component of a normal difference quadratic. -/
theorem abs_inner_normal_difference_le_sq
    (firstNormal secondNormal referenceNormal : E)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1)
    (hreferenceUnit : ‖referenceNormal‖ = 1) :
    |inner ℝ referenceNormal (secondNormal - firstNormal)| ≤
      (max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖) ^ 2 := by
  have hfirstSquare := norm_sub_sq_real firstNormal referenceNormal
  have hsecondSquare := norm_sub_sq_real secondNormal referenceNormal
  rw [hfirstUnit, hreferenceUnit, real_inner_comm referenceNormal firstNormal] at hfirstSquare
  rw [hsecondUnit, hreferenceUnit, real_inner_comm referenceNormal secondNormal] at hsecondSquare
  have hfirstBound : ‖firstNormal - referenceNormal‖ ^ 2 ≤
      (max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_left _ _))).mpr (le_max_left _ _)
  have hsecondBound : ‖secondNormal - referenceNormal‖ ^ 2 ≤
      (max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) (le_max_right _ _))).mpr (le_max_right _ _)
  rw [inner_sub_right]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg ‖firstNormal - referenceNormal‖,
    sq_nonneg ‖secondNormal - referenceNormal‖]

/-- The normal component of a radial difference has a quadratic normal-field error. -/
theorem abs_inner_radial_difference_le
    (firstNormal secondNormal referenceNormal : E) (firstRadius secondRadius : ℝ)
    (hfirstRadius : 0 ≤ firstRadius)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1)
    (hreferenceUnit : ‖referenceNormal‖ = 1) :
    |inner ℝ referenceNormal (secondRadius • secondNormal - firstRadius • firstNormal)| ≤
      |secondRadius - firstRadius| + max firstRadius secondRadius *
        (max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖) ^ 2 := by
  have hdecomposition : secondRadius • secondNormal - firstRadius • firstNormal =
      (secondRadius - firstRadius) • secondNormal + firstRadius • (secondNormal - firstNormal) := by
    module
  have hnormal := abs_inner_normal_difference_le_sq firstNormal secondNormal referenceNormal
    hfirstUnit hsecondUnit hreferenceUnit
  have hunitBound : |inner ℝ referenceNormal secondNormal| ≤ 1 := by
    simpa only [hreferenceUnit, hsecondUnit, mul_one] using
      abs_real_inner_le_norm referenceNormal secondNormal
  have hfirstBound := mul_le_mul_of_nonneg_left hunitBound (abs_nonneg (secondRadius - firstRadius))
  have hsecondBound := mul_le_mul_of_nonneg_left hnormal hfirstRadius
  have hmaximumBound := mul_le_mul_of_nonneg_right (le_max_left firstRadius secondRadius)
    (sq_nonneg (max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖))
  have hsum := abs_add_le ((secondRadius - firstRadius) * inner ℝ referenceNormal secondNormal)
    (firstRadius * inner ℝ referenceNormal (secondNormal - firstNormal))
  rw [abs_mul, abs_mul, abs_of_nonneg hfirstRadius] at hsum
  rw [hdecomposition, inner_add_right, inner_smul_right, inner_smul_right]
  linarith

/-- The normal component of a recipient chord splits into the source and radius errors. -/
theorem abs_inner_recipient_chord_le
    (firstCenter secondCenter first second firstNormal secondNormal referenceNormal : E)
    (firstRadius secondRadius : ℝ) (hfirstRadius : 0 ≤ firstRadius)
    (hfirstUnit : ‖firstNormal‖ = 1) (hsecondUnit : ‖secondNormal‖ = 1)
    (hreferenceUnit : ‖referenceNormal‖ = 1)
    (hfirstPosition : first = firstCenter + firstRadius • firstNormal)
    (hsecondPosition : second = secondCenter + secondRadius • secondNormal) :
    |inner ℝ referenceNormal (second - first)| ≤
      |inner ℝ referenceNormal (secondCenter - firstCenter)| + |secondRadius - firstRadius| +
        max firstRadius secondRadius *
          (max ‖firstNormal - referenceNormal‖ ‖secondNormal - referenceNormal‖) ^ 2 := by
  have hdecomposition : second - first = secondCenter - firstCenter +
      (secondRadius • secondNormal - firstRadius • firstNormal) := by
    rw [hfirstPosition, hsecondPosition]
    module
  have hradial := abs_inner_radial_difference_le firstNormal secondNormal referenceNormal
    firstRadius secondRadius hfirstRadius hfirstUnit hsecondUnit hreferenceUnit
  rw [hdecomposition, inner_add_right]
  have hsum := abs_add_le (inner ℝ referenceNormal (secondCenter - firstCenter))
    (inner ℝ referenceNormal (secondRadius • secondNormal - firstRadius • firstNormal))
  linarith

end BoundedUncertainty
