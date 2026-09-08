import BoundedUncertainty.DualInflation
import BoundedUncertainty.Section3Interfaces
import BoundedUncertainty.ConstantRadius
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Scope of the distance description of dual inflation

The union definition is equivalent to the weak infimum-distance sublevel
when the distance is attained, in particular for nonempty compact sets or
nonempty closed sets in a proper space. For arbitrary nonclosed sets, boundary
distance may fail to be attained. A constant-radius open-ball counterexample
is proved below. The real-valued infDist convention for the empty set is also
recorded explicitly and is not used as an extended-real distance convention.
-/

namespace BoundedUncertainty

open Set Topology

section DistanceScope

variable {E : Type*} [NormedAddCommGroup E]

/-- Membership always gives the weak infimum-distance inequality. -/
theorem dualInflation_subset_infDist_sublevel (radius : E → ℝ) (A : Set E) :
    dualInflation radius A ⊆ {y | Metric.infDist y A ≤ radius y} := by
  intro y hy
  obtain ⟨x, hx, hdistance⟩ := (mem_dualInflation radius A y).mp hy
  exact (Metric.infDist_le_dist_of_mem hx).trans ((dist_comm y x).trans_le hdistance)

/-- A strict distance inequality is sufficient without closedness, provided the set is nonempty. -/
theorem infDist_strict_sublevel_subset_dualInflation
    (radius : E → ℝ) (A : Set E) (hne : A.Nonempty) :
    {y | Metric.infDist y A < radius y} ⊆ dualInflation radius A := by
  intro y hy
  obtain ⟨x, hx, hdistance⟩ := (Metric.infDist_lt_iff hne).mp hy
  exact (mem_dualInflation radius A y).mpr
    ⟨x, hx, (dist_comm x y).trans_le hdistance.le⟩

/-- Distance attainment is sufficient to justify the weak-sublevel description. -/
theorem dualInflation_eq_infDist_sublevel_of_attained
    (radius : E → ℝ) (A : Set E)
    (hattained : ∀ y : E, ∃ x ∈ A, Metric.infDist y A = dist y x) :
    dualInflation radius A = {y | Metric.infDist y A ≤ radius y} := by
  apply Subset.antisymm (dualInflation_subset_infDist_sublevel radius A)
  intro y hy
  obtain ⟨x, hx, hdistance⟩ := hattained y
  exact (mem_dualInflation radius A y).mpr
    ⟨x, hx, (dist_comm x y).trans_le (hdistance ▸ hy)⟩

/-- Corrected weak-distance equality for a nonempty compact input set. -/
theorem dualInflation_eq_infDist_sublevel_of_isCompact
    (radius : E → ℝ) (A : Set E) (hcompact : IsCompact A) (hne : A.Nonempty) :
    dualInflation radius A = {y | Metric.infDist y A ≤ radius y} :=
  dualInflation_eq_infDist_sublevel_of_attained radius A
    (fun y => hcompact.exists_infDist_eq_dist hne y)

/-- Closedness suffices in a proper metric space, still with nonemptiness explicit. -/
theorem dualInflation_eq_infDist_sublevel_of_isClosed [ProperSpace E]
    (radius : E → ℝ) (A : Set E) (hclosed : IsClosed A) (hne : A.Nonempty) :
    dualInflation radius A = {y | Metric.infDist y A ≤ radius y} :=
  dualInflation_eq_infDist_sublevel_of_attained radius A
    (fun y => hclosed.exists_infDist_eq_dist hne y)

/-- The corrected distance formula also gives the corresponding actual dual set map. -/
theorem dualSetMap_eq_infDist_sublevel_of_isCompact
    (f : E → E) (radius : E → ℝ) (A : Set E) (hcompact : IsCompact A) (hne : A.Nonempty) :
    dualSetMap f radius A = {y | Metric.infDist (f y) A ≤ radius (f y)} := by
  rw [dualSetMap_eq_preimage, dualInflation_eq_infDist_sublevel_of_isCompact radius A hcompact hne]
  rfl

/-- Real-valued infDist assigns zero to the empty set; this is a separate convention. -/
theorem infDist_sublevel_empty_of_nonneg (radius : E → ℝ) (hradius : ∀ y, 0 ≤ radius y) :
    {y | Metric.infDist y (∅ : Set E) ≤ radius y} = univ := by
  ext y
  simp only [mem_setOf_eq, Metric.infDist_empty, mem_univ, iff_true]
  exact hradius y

end DistanceScope

section OpenBallCounterexample

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every point of the open unit ball is strictly more than distance one from 2u. -/
theorem one_lt_dist_two_smul_of_mem_unitBall (u x : E) (hu : ‖u‖ = 1)
    (hx : x ∈ Metric.ball (0 : E) 1) : 1 < dist ((2 : ℝ) • u) x := by
  have htriangle := dist_triangle ((2 : ℝ) • u) x (0 : E)
  have hnorm : dist ((2 : ℝ) • u) (0 : E) = 2 := by
    rw [dist_zero_right, norm_smul, Real.norm_ofNat, hu, mul_one]
  rw [hnorm] at htriangle
  change dist x (0 : E) < 1 at hx
  linarith

/-- The distance infimum is one, but no point of the open unit ball attains it. -/
theorem infDist_two_smul_unitBall (u : E) (hu : ‖u‖ = 1) :
    Metric.infDist ((2 : ℝ) • u) (Metric.ball (0 : E) 1) = 1 := by
  have hnonempty : (Metric.ball (0 : E) 1).Nonempty :=
    ⟨0, by simp only [Metric.mem_ball, dist_self]; norm_num⟩
  apply le_antisymm
  · have huclosure : u ∈ closure (Metric.ball (0 : E) 1) := by
      rw [closure_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)]
      simpa only [Metric.mem_closedBall, dist_zero_right, hu] using (le_rfl : (1 : ℝ) ≤ 1)
    have hdistance : dist ((2 : ℝ) • u) u = 1 := by
      rw [dist_eq_norm]
      have hvector : (2 : ℝ) • u - u = u := by simp only [two_smul, add_sub_cancel_right]
      rw [hvector, hu]
    calc
      Metric.infDist ((2 : ℝ) • u) (Metric.ball (0 : E) 1) =
          Metric.infDist ((2 : ℝ) • u) (closure (Metric.ball (0 : E) 1)) :=
        Metric.infDist_closure.symm
      _ ≤ dist ((2 : ℝ) • u) u := Metric.infDist_le_dist_of_mem huclosure
      _ = 1 := hdistance
  · apply (Metric.le_infDist hnonempty).mpr
    intro x hx
    exact (one_lt_dist_two_smul_of_mem_unitBall u x hu hx).le

/-- Constant positive radius one does not include the unattained limiting center. -/
theorem two_smul_not_mem_dualInflation_unitBall (u : E) (hu : ‖u‖ = 1) :
    (2 : ℝ) • u ∉ dualInflation (fun _ : E => (1 : ℝ)) (Metric.ball (0 : E) 1) := by
  intro hmem
  obtain ⟨x, hx, hdistance⟩ := (mem_dualInflation _ _ _).mp hmem
  have hstrict := one_lt_dist_two_smul_of_mem_unitBall u x hu hx
  exact hstrict.not_ge ((dist_comm ((2 : ℝ) • u) x).trans_le hdistance)

/-- A Lean counterexample to the arbitrary-set equality in Definition 4.13 / Lemma 4.15. -/
theorem dualInflation_unitBall_ne_infDist_sublevel (u : E) (hu : ‖u‖ = 1) :
    dualInflation (fun _ : E => (1 : ℝ)) (Metric.ball (0 : E) 1) ≠
      {y | Metric.infDist y (Metric.ball (0 : E) 1) ≤ 1} := by
  intro heq
  apply two_smul_not_mem_dualInflation_unitBall u hu
  rw [heq]
  exact (infDist_two_smul_unitBall u hu).le

end OpenBallCounterexample

section ConstantRadius

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The counterexample radius obeys positive uniform bounds and has actual gradient zero. -/
theorem constantRadius_one_dual_bounds_and_gradient (y : E) :
    0 < (fun _ : E => (1 : ℝ)) y ∧
      1 ≤ (fun _ : E => (1 : ℝ)) y ∧ (fun _ : E => (1 : ℝ)) y ≤ 1 ∧
      HasGradientAt (fun _ : E => (1 : ℝ)) (0 : E) y ∧
      ‖gradient (fun _ : E => (1 : ℝ)) y‖ < 1 := by
  refine ⟨by norm_num, le_rfl, le_rfl, hasGradientAt_const _ _, ?_⟩
  rw [gradient_fun_const, norm_zero]
  norm_num

end ConstantRadius

/-- A whole-space identity system with strictly positive constant radius one. -/
noncomputable def identityUnitRadiusSystem :
    SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) 1 1 where
  dimension_at_least_two := by simp
  domain := univ
  regular_closed := by simp [IsRegularClosed]
  map := id
  radius := fun _ => 1
  radius_bound := 1
  radius_bound_pos := zero_lt_one
  radius_order_pos := le_rfl
  map_order_pos := le_rfl
  map_into_domain := mapsTo_univ _ _
  diffeomorphism := ambientDiffeomorphismOn_id 1 univ
  radius_extension := hasLocalExtensionOn_of_contDiff 1 univ (fun _ => 1) contDiff_const
  radius_nonneg := fun _ _ => zero_le_one
  radius_le_bound := fun _ _ => le_rfl
  ball_into_domain := fun _ _ => subset_univ _

/-- The failure occurs in an admissible two-dimensional whole-space system,
with an actual self-diffeomorphism and positive radius, even under contraction. -/
theorem exists_system_dualInflation_ne_infDist_sublevel :
    ∃ system : SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) 1 1,
      system.domain = univ ∧ system.map = id ∧ system.IsContraction ∧
      (∀ y, system.radius y = 1) ∧
      dualInflation system.radius (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≠
        {y | Metric.infDist y (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≤ system.radius y} := by
  refine ⟨identityUnitRadiusSystem, rfl, rfl,
    identityUnitRadiusSystem.isContraction_of_constant_radius 1 (fun _ _ => rfl),
    fun _ => rfl, ?_⟩
  exact dualInflation_unitBall_ne_infDist_sublevel
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (by simp)

end BoundedUncertainty
