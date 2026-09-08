import BoundedUncertainty.DualInflationScope
import BoundedUncertainty.SourceVisibility
import BoundedUncertainty.SphereBoundary
import BoundedUncertainty.BoundaryDefiningGraph

/-!
The annulus counterexample accompanying Assumption 4.1. For the actual
whole-plane identity system with radius one, the annulus with inner radius
one and outer radius two inflates to the closed ball of radius three. Every
point of the inner boundary has its entire constituent ball in the interior
of that image, so source visibility is not automatic.
-/

namespace BoundedUncertainty

open Set Metric

/-- The closed annulus in the manuscript's visibility example. -/
def visibilityAnnulus : Set (EuclideanSpace ℝ (Fin 2)) :=
  closedBall 0 2 \ ball 0 1

theorem mem_visibilityAnnulus (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ visibilityAnnulus ↔ 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  simp only [visibilityAnnulus, mem_diff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
  exact and_comm

theorem isCompact_visibilityAnnulus : IsCompact visibilityAnnulus :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2).diff isOpen_ball

theorem interior_visibilityAnnulus :
    interior visibilityAnnulus = {x | 1 < ‖x‖ ∧ ‖x‖ < 2} := by
  rw [visibilityAnnulus, diff_eq, interior_inter, interior_closedBall _ (by norm_num : (2 : ℝ) ≠ 0),
    interior_compl, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  ext x
  simp only [mem_inter_iff, mem_ball, mem_compl_iff, mem_closedBall, dist_zero_right,
    mem_setOf_eq, not_le]
  exact and_comm

theorem isRegularClosed_visibilityAnnulus : IsRegularClosed visibilityAnnulus := by
  have hcover : Codisjoint
      (interior (ball (0 : EuclideanSpace ℝ (Fin 2)) 2))
      (interior (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ) := by
    rw [isOpen_ball.interior_eq, isClosed_closedBall.isOpen_compl.interior_eq,
      codisjoint_iff_le_sup]
    intro x _
    by_cases hx : ‖x‖ < 2
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using
        (show 1 < ‖x‖ by linarith))
  change closure (interior visibilityAnnulus) = visibilityAnnulus
  have hinterior : interior visibilityAnnulus =
      ball (0 : EuclideanSpace ℝ (Fin 2)) 2 ∩ (closedBall 0 1)ᶜ := by
    rw [interior_visibilityAnnulus]
    ext x
    simp only [mem_inter_iff, mem_ball, mem_compl_iff, mem_closedBall, dist_zero_right,
      mem_setOf_eq, not_le]
    exact and_comm
  rw [hinterior, closure_inter_of_codisjoint_interior hcover,
    closure_ball _ (by norm_num : (2 : ℝ) ≠ 0), closure_compl,
    interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  rfl

theorem mem_frontier_visibilityAnnulus (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ frontier visibilityAnnulus ↔ ‖x‖ = 1 ∨ ‖x‖ = 2 := by
  rw [frontier, isCompact_visibilityAnnulus.isClosed.closure_eq, mem_diff,
    mem_visibilityAnnulus, interior_visibilityAnnulus]
  simp only [mem_setOf_eq]
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hnot⟩
    by_cases hinner : ‖x‖ = 1
    · exact Or.inl hinner
    · exact Or.inr (by by_contra houter; exact hnot ⟨lt_of_le_of_ne hlower (Ne.symm hinner),
        lt_of_le_of_ne hupper houter⟩)
  · rintro (hinner | houter)
    · rw [hinner]
      norm_num
    · rw [houter]
      norm_num

theorem visibilityAnnulus_nonempty : visibilityAnnulus.Nonempty := by
  refine ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_⟩
  rw [mem_visibilityAnnulus]
  norm_num

/-- Radial rescaling has exactly the prescribed positive norm and radial distance. -/
theorem annulus_radial_rescaling (x : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (hx : 0 < ‖x‖) (hradius : 0 ≤ radius) :
    ‖(radius / ‖x‖) • x‖ = radius ∧
      dist x ((radius / ‖x‖) • x) = |‖x‖ - radius| := by
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hradius hx.le),
      div_mul_cancel₀ _ (ne_of_gt hx)]
  · rw [dist_eq_norm]
    have heq : x - (radius / ‖x‖) • x = (1 - radius / ‖x‖) • x := by module
    rw [heq, norm_smul, Real.norm_eq_abs]
    calc
      |1 - radius / ‖x‖| * ‖x‖ = |(1 - radius / ‖x‖) * ‖x‖| := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg x)]
      _ = |‖x‖ - radius| := by
        congr 1
        field_simp [ne_of_gt hx]

/-- The hole is completely filled, and the outer radius increases by one. -/
theorem inflation_visibilityAnnulus :
    inflation (fun _ : EuclideanSpace ℝ (Fin 2) => 1) visibilityAnnulus = closedBall 0 3 := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hx, hdist⟩ := mem_iUnion.mp hz
    have hnorm := (mem_visibilityAnnulus x).mp hx
    rw [mem_closedBall, dist_zero_right]
    have htriangle := norm_le_norm_sub_add z x
    rw [← dist_eq_norm] at htriangle
    linarith [(show dist z x ≤ 1 from hdist)]
  · intro hz
    have hzbound : ‖z‖ ≤ 3 := by simpa using hz
    by_cases hzero : z = 0
    · rw [hzero]
      apply mem_iUnion.mpr
      refine ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ), mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · rw [mem_visibilityAnnulus]
        norm_num
      · simp
    have hzpositive : 0 < ‖z‖ := norm_pos_iff.mpr hzero
    by_cases hsmall : ‖z‖ < 1
    · obtain ⟨hnorm, hdist⟩ := annulus_radial_rescaling z 1 hzpositive (by norm_num)
      apply mem_iUnion.mpr
      refine ⟨(1 / ‖z‖) • z, mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · rw [mem_visibilityAnnulus, hnorm]
        norm_num
      · rw [mem_closedBall, hdist, abs_of_nonpos (by linarith)]
        linarith
    by_cases hlarge : 2 < ‖z‖
    · obtain ⟨hnorm, hdist⟩ := annulus_radial_rescaling z 2 hzpositive (by norm_num)
      apply mem_iUnion.mpr
      refine ⟨(2 / ‖z‖) • z, mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · rw [mem_visibilityAnnulus, hnorm]
        norm_num
      · rw [mem_closedBall, hdist, abs_of_nonneg (by linarith)]
        linarith
    · apply mem_iUnion.mpr
      refine ⟨z, mem_iUnion.mpr ⟨?_, mem_closedBall_self (by norm_num)⟩⟩
      rw [mem_visibilityAnnulus]
      exact ⟨le_of_not_gt hsmall, le_of_not_gt hlarge⟩

/-- One global polynomial defining function describes both smooth boundary components. -/
theorem visibilityAnnulus_defining_nonpos_iff (x : EuclideanSpace ℝ (Fin 2)) :
    (‖x‖ ^ 2 - 1) * (‖x‖ ^ 2 - 4) ≤ 0 ↔ x ∈ visibilityAnnulus := by
  rw [mem_visibilityAnnulus]
  constructor
  · intro hproduct
    rcases mul_nonpos_iff.mp hproduct with hcase | hcase
    · constructor <;> nlinarith [norm_nonneg x]
    · nlinarith [norm_nonneg x]
  · rintro ⟨hlower, hupper⟩
    apply mul_nonpos_of_nonneg_of_nonpos <;> nlinarith [norm_nonneg x]

theorem hasGradientAt_visibilityAnnulus_defining (x : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (fun z : EuclideanSpace ℝ (Fin 2) => (‖z‖ ^ 2 - 1) * (‖z‖ ^ 2 - 4))
      ((4 * ‖x‖ ^ 2 - 10) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((hasFDerivAt_id x).norm_sq.sub_const (1 : ℝ)).mul
    ((hasFDerivAt_id x).norm_sq.sub_const (4 : ℝ))) using 1
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, id_eq]
  ring

/-- The annulus satisfies the original smooth-boundary hypothesis despite failing visibility. -/
noncomputable def visibilityAnnulusBoundary (x : frontier visibilityAnnulus) :
    C1BoundaryAt visibilityAnnulus x := by
  have hnorm := (mem_frontier_visibilityAnnulus x).mp x.property
  refine C1BoundaryAt.ofDefiningFunction visibilityAnnulus x univ isOpen_univ (mem_univ _)
    (fun z : EuclideanSpace ℝ (Fin 2) => (‖z‖ ^ 2 - 1) * (‖z‖ ^ 2 - 4))
    (((contDiff_id.norm_sq ℝ).sub contDiff_const).mul
      ((contDiff_id.norm_sq ℝ).sub contDiff_const)).contDiffOn ?_
    (fun z _ => (visibilityAnnulus_defining_nonpos_iff z).symm)
    ((4 * ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2 - 10) • (x : EuclideanSpace ℝ (Fin 2)))
    (hasGradientAt_visibilityAnnulus_defining x) ?_
  · rcases hnorm with hnorm | hnorm <;> norm_num [hnorm]
  · apply smul_ne_zero
    · rcases hnorm with hnorm | hnorm <;> rw [hnorm] <;> norm_num
    · intro hzero
      simp only [hzero, norm_zero] at hnorm
      norm_num at hnorm

/-- A common one-dimensional graph model realizes both boundary circles. -/
noncomputable def visibilityAnnulusFrontierGraph (x : frontier visibilityAnnulus) :
    C1FrontierGraphAt (F := Fin 1 → ℝ) visibilityAnnulus x := by
  have hdimension : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1 = 1 := by simp
  have chart := fixedModelFrontierGraph isRegularClosed_visibilityAnnulus visibilityAnnulusBoundary x
  rw [hdimension] at chart
  exact chart

theorem identityUnitRadiusSystem_image_visibilityAnnulus :
    setValuedImage identityUnitRadiusSystem.map identityUnitRadiusSystem.radius visibilityAnnulus =
      closedBall 0 3 := by
  simpa only [setValuedImage_eq_inflation, identityUnitRadiusSystem, image_id] using
    inflation_visibilityAnnulus

/-- Every inner-boundary constituent ball is strictly inside the recipient set. -/
theorem innerBoundary_ball_subset_interior_image_visibilityAnnulus
    (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖ = 1) :
    closedBall (identityUnitRadiusSystem.map x)
      (identityUnitRadiusSystem.radius (identityUnitRadiusSystem.map x)) ⊆
      interior (setValuedImage identityUnitRadiusSystem.map identityUnitRadiusSystem.radius
        visibilityAnnulus) := by
  intro z hz
  rw [identityUnitRadiusSystem_image_visibilityAnnulus,
    interior_closedBall _ (by norm_num : (3 : ℝ) ≠ 0)]
  change dist z 0 < 3
  rw [dist_zero_right]
  have hball : dist z x ≤ 1 := hz
  have htriangle := norm_le_norm_sub_add z x
  rw [← dist_eq_norm, hx] at htriangle
  linarith

theorem identityUnitRadiusSystem_not_sourceVisible_visibilityAnnulus :
    ¬ identityUnitRadiusSystem.SourceVisible visibilityAnnulus := by
  intro hvisible
  have hnorm : ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1 := by simp
  obtain ⟨z, hball, hfrontier⟩ := hvisible (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    ((mem_frontier_visibilityAnnulus _).mpr (Or.inl hnorm))
  exact (disjoint_interior_frontier.notMem_of_mem_left
    (innerBoundary_ball_subset_interior_image_visibilityAnnulus _ hnorm hball)) hfrontier

/-- A concrete admissible contraction with compact, regular closed, C1 source boundary
fails the source-visibility assumption exactly as in the manuscript's annulus example. -/
theorem annulus_visibility_counterexample :
    identityUnitRadiusSystem.domain = univ ∧ identityUnitRadiusSystem.map = id ∧
      identityUnitRadiusSystem.IsContraction ∧
      visibilityAnnulus.Nonempty ∧ IsCompact visibilityAnnulus ∧
      IsRegularClosed visibilityAnnulus ∧
      (∀ x : frontier visibilityAnnulus, Nonempty (C1FrontierGraphAt (F := Fin 1 → ℝ)
        visibilityAnnulus x)) ∧
      setValuedImage identityUnitRadiusSystem.map identityUnitRadiusSystem.radius visibilityAnnulus =
        closedBall 0 3 ∧ ¬ identityUnitRadiusSystem.SourceVisible visibilityAnnulus := by
  exact ⟨rfl, rfl, identityUnitRadiusSystem.isContraction_of_constant_radius 1 (fun _ _ => rfl),
    visibilityAnnulus_nonempty, isCompact_visibilityAnnulus, isRegularClosed_visibilityAnnulus,
    (fun x => ⟨visibilityAnnulusFrontierGraph x⟩), identityUnitRadiusSystem_image_visibilityAnnulus,
    identityUnitRadiusSystem_not_sourceVisible_visibilityAnnulus⟩

end BoundedUncertainty
