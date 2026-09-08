import BoundedUncertainty.SIRSDeterministic
import BoundedUncertainty.SIRSInvariance
import BoundedUncertainty.Section3Interfaces
import BoundedUncertainty.DegenerateNormal
import BoundedUncertainty.BoundaryMap

/-! Example 3.13 as an actual Definition 3.1 system, with its canonical gradient.
The zero-radius boundary witness supplies Remark 3.16 in dimension two. -/
namespace BoundedUncertainty
open Set

noncomputable def sirsSystem (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) :
    SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) r s where
  dimension_at_least_two := by simp
  domain := sirsSimplex
  regular_closed := isRegularClosed_sirsSimplex
  map := sirsMap (1 / 10) 1 3
  radius := sirsRadius κ
  radius_bound := κ / 10 + 1
  radius_bound_pos := by positivity
  radius_order_pos := hr
  map_order_pos := hs
  map_into_domain := sirsMap_mapsTo
  diffeomorphism := sirsAmbientDiffeomorphism s
  radius_extension := hasLocalExtensionOn_of_contDiff r sirsSimplex (sirsRadius κ)
    (contDiff_sirsRadius κ r)
  radius_nonneg := sirsRadius_nonneg κ hκ
  radius_le_bound := sirsRadius_le_bound κ hκ
  ball_into_domain := fun x hx => sirs_closedBall_subset κ hκ hthreshold _ (sirsMap_mapsTo hx)

theorem sirsSystem_radiusGradient (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) (p : sirsSimplex) :
    (sirsSystem r s hr hs κ hκ hthreshold).radiusGradient p = sirsRadiusGradient κ p := by
  let extension : LocalExtensionAt 1 sirsSimplex (sirsRadius κ) (p : EuclideanSpace ℝ (Fin 2)) := {
    neighborhood := univ
    isOpen_neighborhood := isOpen_univ
    mem_neighborhood := mem_univ _
    extension := sirsRadius κ
    contDiffOn_extension := (contDiff_sirsRadius κ 1).contDiffOn
    agrees := fun _ _ => rfl
  }
  rw [(sirsSystem r s hr hs κ hκ hthreshold).radiusGradient_eq_extension
    (by decide : 1 ≤ 1) extension p (mem_univ _)]
  exact gradient_sirsRadius κ p

theorem sirsSystem_isContraction (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) :
    (sirsSystem r s hr hs κ hκ hthreshold).IsContraction := by
  intro p
  rw [sirsSystem_radiusGradient]
  exact (sirsRadiusGradient_norm_le κ hκ p p.property).trans_lt
    ((div_lt_one (by positivity : 0 < 20 * Real.sqrt (2 : ℝ))).mpr hthreshold)

theorem sirsSystem_gradient_supremum (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) :
    IsGreatest (range (fun p : sirsSimplex =>
      ‖(sirsSystem r s hr hs κ hκ hthreshold).radiusGradient p‖))
      ((κ / 10) / (2 * Real.sqrt 2)) := by
  have hvalue : (κ / 10) / (2 * Real.sqrt 2) = κ / (20 * Real.sqrt 2) := by ring
  rw [hvalue]
  constructor
  · refine ⟨⟨!₂[(1 : ℝ) / 2, 1 / 2], by norm_num [sirsSimplex]⟩, ?_⟩
    simpa only [sirsSystem_radiusGradient] using sirsRadiusGradient_norm_attained κ hκ
  · rintro value ⟨p, rfl⟩
    simpa only [sirsSystem_radiusGradient] using sirsRadiusGradient_norm_le κ hκ p p.property

noncomputable def sirsSystemThree : SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) 2 2 :=
  sirsSystem 2 2 (by decide) (by decide) 3 (by norm_num)
    (lt_trans (by norm_num : (3 : ℝ) < 2828 / 100) sirs_numeric_threshold)

theorem sirsSystemThree_isContraction : sirsSystemThree.IsContraction :=
  sirsSystem_isContraction _ _ _ _ _ _ _

theorem sirsSystemThree_boundary_zero_nonzero_gradient :
    (!₂[(1 : ℝ) / 2, 0] : EuclideanSpace ℝ (Fin 2)) ∈ frontier sirsSystemThree.domain ∧
    sirsSystemThree.radius !₂[(1 : ℝ) / 2, 0] = 0 ∧
    sirsSystemThree.radiusGradient ⟨!₂[(1 : ℝ) / 2, 0], by norm_num [sirsSystemThree, sirsSystem, sirsSimplex]⟩ =
      !₂[0, (3 : ℝ) / 40] := by
  refine ⟨(mem_frontier_sirsSimplex _).mpr ⟨by norm_num [sirsSimplex], Or.inr (Or.inl (by simp))⟩,
    by norm_num [sirsSystemThree, sirsSystem, sirsRadius], ?_⟩
  change (sirsSystem 2 2 _ _ 3 _ _).radiusGradient _ = _
  rw [sirsSystem_radiusGradient]
  ext i
  fin_cases i <;> norm_num [sirsRadiusGradient]

/-- An actual admissible, contracting two-dimensional system whose zero-radius boundary
centre keeps its position but changes its normal. -/
theorem exists_system_boundary_zero_radius_normal_changes :
    ∃ system : SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) 2 2,
      system.IsContraction ∧ ∃ p : system.domain, ∃ n : EuclideanSpace ℝ (Fin 2),
        (p : EuclideanSpace ℝ (Fin 2)) ∈ frontier system.domain ∧ system.radius p = 0 ∧
        system.radiusGradient p ≠ 0 ∧ ‖n‖ = 1 ∧
        exponentialMap system.radius system.radiusGradientOnAmbient ((p : EuclideanSpace ℝ (Fin 2)), n) ≠
          ((p : EuclideanSpace ℝ (Fin 2)), n) := by
  refine ⟨sirsSystemThree, sirsSystemThree_isContraction,
    ⟨!₂[(1 : ℝ) / 2, 0], by norm_num [sirsSystemThree, sirsSystem, sirsSimplex]⟩, !₂[1, 0],
    sirsSystemThree_boundary_zero_nonzero_gradient.1,
    sirsSystemThree_boundary_zero_nonzero_gradient.2.1, ?_, ?_, ?_⟩
  · rw [sirsSystemThree_boundary_zero_nonzero_gradient.2.2]
    intro heq
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) heq
    norm_num at this
  · norm_num [EuclideanSpace.norm_eq]
  · intro heq
    have hnormal := congrArg (fun output : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => output.2) heq
    change normalUpdate (sirsSystemThree.radiusGradientOnAmbient !₂[(1 : ℝ) / 2, 0]) !₂[1, 0] = !₂[1, 0] at hnormal
    rw [sirsSystemThree.radiusGradientOnAmbient_apply
      ⟨!₂[(1 : ℝ) / 2, 0], by norm_num [sirsSystemThree, sirsSystem, sirsSimplex]⟩,
      sirsSystemThree_boundary_zero_nonzero_gradient.2.2] at hnormal
    apply normalUpdate_ne_self_of_orthogonal (!₂[0, (3 : ℝ) / 40] : EuclideanSpace ℝ (Fin 2))
      !₂[1, 0] _ _ hnormal
    · intro heq
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) heq
      norm_num at this
    · norm_num [PiLp.inner_apply, Fin.sum_univ_two]

end BoundedUncertainty
