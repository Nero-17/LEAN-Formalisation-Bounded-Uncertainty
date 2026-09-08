import BoundedUncertainty.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith

/-!
The topological part of the hypersurface-to-domain bridge. A regular closed
set whose frontier is a coordinate hyperplane in a ball occupies precisely
one closed half of that ball. Neither orientation nor a normal is assumed.
-/

namespace BoundedUncertainty

open Set Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem IsRegularClosed.preimage_homeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (hB : IsRegularClosed B) (coordinates : (ℝ × F) ≃ₜ E) :
    IsRegularClosed (coordinates ⁻¹' B) := by
  unfold IsRegularClosed at *
  rw [← coordinates.preimage_interior, ← coordinates.preimage_closure, hB]

omit [NormedSpace ℝ F] in
theorem isPreconnected_subset_interior_or_compl {B S : Set (ℝ × F)}
    (hB : IsClosed B) (hS : IsPreconnected S)
    (hfrontier : ∀ z ∈ S, z ∉ frontier B) :
    S ⊆ interior B ∨ S ⊆ Bᶜ := by
  apply hS.subset_or_subset isOpen_interior hB.isOpen_compl
  · exact disjoint_compl_right.mono_left interior_subset
  · intro z hz
    by_cases hzB : z ∈ B
    · left
      rw [← self_diff_frontier B]
      exact ⟨hzB, hfrontier z hz⟩
    · exact Or.inr hzB

/-- Flat frontier graphs determine a side, using regular closedness essentially. -/
theorem one_sided_of_frontier_flat (B : Set (ℝ × F)) (hB : IsRegularClosed B)
    (radius : ℝ) (hradius : 0 < radius)
    (hfrontier : ∀ z ∈ Metric.ball (0 : ℝ × F) radius,
      z ∈ frontier B ↔ z.1 = 0) :
    (∀ z ∈ Metric.ball (0 : ℝ × F) radius, z ∈ B ↔ z.1 ≤ 0) ∨
      (∀ z ∈ Metric.ball (0 : ℝ × F) radius, z ∈ B ↔ 0 ≤ z.1) := by
  have hzero : (0 : ℝ × F) ∈ Metric.ball 0 radius := Metric.mem_ball_self hradius
  have hzeroFrontier : (0 : ℝ × F) ∈ frontier B := (hfrontier 0 hzero).2 rfl
  have hnegative := isPreconnected_subset_interior_or_compl hB.isClosed
    (((convex_ball (0 : ℝ × F) radius).inter
      ((convex_Iio (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ F))).isPreconnected)
    (by
      intro z hz hzf
      have := (hfrontier z hz.1).1 hzf
      exact (ne_of_lt hz.2) this)
  have hpositive := isPreconnected_subset_interior_or_compl hB.isClosed
    (((convex_ball (0 : ℝ × F) radius).inter
      ((convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ F))).isPreconnected)
    (by
      intro z hz hzf
      have := (hfrontier z hz.1).1 hzf
      exact (ne_of_gt hz.2) this)
  have hnotBothInterior
      (hnegative : Metric.ball (0 : ℝ × F) radius ∩ {z | z.1 < 0} ⊆ interior B)
      (hpositive : Metric.ball (0 : ℝ × F) radius ∩ {z | 0 < z.1} ⊆ interior B) : False := by
    have hball : Metric.ball (0 : ℝ × F) radius ⊆ B := by
      intro z hz
      rcases lt_trichotomy z.1 0 with hlt | heq | hgt
      · exact interior_subset (hnegative ⟨hz, hlt⟩)
      · exact hB.isClosed.frontier_subset ((hfrontier z hz).2 heq)
      · exact interior_subset (hpositive ⟨hz, hgt⟩)
    exact hzeroFrontier.2 (interior_maximal hball Metric.isOpen_ball hzero)
  have hnotBothExterior
      (hnegative : Metric.ball (0 : ℝ × F) radius ∩ {z | z.1 < 0} ⊆ Bᶜ)
      (hpositive : Metric.ball (0 : ℝ × F) radius ∩ {z | 0 < z.1} ⊆ Bᶜ) : False := by
    have hzeroClosure : (0 : ℝ × F) ∈ closure (interior B) := by
      rw [hB]
      exact hB.isClosed.frontier_subset hzeroFrontier
    obtain ⟨z, hzball, hzinterior⟩ := mem_closure_iff_nhds.mp hzeroClosure
      (Metric.ball 0 radius) (Metric.isOpen_ball.mem_nhds hzero)
    rcases lt_trichotomy z.1 0 with hlt | heq | hgt
    · exact hnegative ⟨hzball, hlt⟩ (interior_subset hzinterior)
    · exact ((hfrontier z hzball).2 heq).2 hzinterior
    · exact hpositive ⟨hzball, hgt⟩ (interior_subset hzinterior)
  rcases hnegative with hnegative | hnegative <;>
    rcases hpositive with hpositive | hpositive
  · exact (hnotBothInterior hnegative hpositive).elim
  · left
    intro z hz
    constructor
    · intro hzB
      by_contra h
      exact hpositive ⟨hz, lt_of_not_ge h⟩ hzB
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact interior_subset (hnegative ⟨hz, hlt⟩)
      · exact hB.isClosed.frontier_subset ((hfrontier z hz).2 heq)
  · right
    intro z hz
    constructor
    · intro hzB
      by_contra h
      exact hnegative ⟨hz, lt_of_not_ge h⟩ hzB
    · intro h
      rcases lt_or_eq_of_le h with hgt | heq
      · exact interior_subset (hpositive ⟨hz, hgt⟩)
      · exact hB.isClosed.frontier_subset ((hfrontier z hz).2 heq.symm)
  · exact (hnotBothExterior hnegative hpositive).elim

end BoundedUncertainty
