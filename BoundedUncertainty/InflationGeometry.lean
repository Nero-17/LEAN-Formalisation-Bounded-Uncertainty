import BoundedUncertainty.Basic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Compact inflation and its boundary contributors

The radius is assumed continuous only on the centre set. Nonnegative radii,
including zero, are allowed. Compactness uses the properness of the ambient
normed space, as holds for the manuscript's finite-dimensional Euclidean space.
The final theorem separates the compactness argument from Lemma 3.4's local
contributor obstruction.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem mem_inflation (ε : E → ℝ) (B : Set E) (z : E) :
    z ∈ inflation ε B ↔ ∃ y ∈ B, dist z y ≤ ε y := by
  simp only [inflation, Set.mem_iUnion, Metric.mem_closedBall, exists_prop]

theorem closedBall_subset_inflation (ε : E → ℝ) (B : Set E) (y : E) (hy : y ∈ B) :
    Metric.closedBall y (ε y) ⊆ inflation ε B := by
  intro z hz
  exact (mem_inflation ε B z).mpr ⟨y, hy, hz⟩

theorem subset_inflation (ε : E → ℝ) (B : Set E) (hε : ∀ y ∈ B, 0 ≤ ε y) :
    B ⊆ inflation ε B := by
  intro y hy
  exact (mem_inflation ε B y).mpr ⟨y, hy, by simpa only [dist_self] using hε y hy⟩

theorem ball_subset_interior_inflation (ε : E → ℝ) (B : Set E) (y : E) (hy : y ∈ B) :
    Metric.ball y (ε y) ⊆ interior (inflation ε B) := by
  intro z hz
  apply interior_mono
    (Metric.ball_subset_closedBall.trans (closedBall_subset_inflation ε B y hy))
  rwa [Metric.isOpen_ball.interior_eq]

/-- A boundary recipient cannot lie strictly inside any constituent ball. -/
theorem radius_le_dist_of_frontier_inflation (ε : E → ℝ) (B : Set E)
    (z y : E) (hz : z ∈ frontier (inflation ε B)) (hy : y ∈ B) :
    ε y ≤ dist z y := by
  apply le_of_not_gt
  intro hlt
  exact hz.2 (ball_subset_interior_inflation ε B y hy hlt)

variable [NormedSpace ℝ E]

/-- A fixed unit closed ball parametrizes every constituent, including a zero-radius ball. -/
theorem inflation_eq_image_prod_closedBall (ε : E → ℝ) (B : Set E)
    (hε : ∀ y ∈ B, 0 ≤ ε y) :
    inflation ε B = (fun p : E × E => p.1 + ε p.1 • p.2) ''
      (B ×ˢ Metric.closedBall (0 : E) 1) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, hzball⟩ := (mem_inflation ε B z).mp hz
    change z ∈ Metric.closedBall y (ε y) at hzball
    rw [← affinity_unitClosedBall (hε y hy) y] at hzball
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hzball
    exact ⟨(y, v), ⟨hy, hv⟩, rfl⟩
  · rintro ⟨⟨y, v⟩, ⟨hy, hv⟩, rfl⟩
    apply closedBall_subset_inflation ε B y hy
    rw [← affinity_unitClosedBall (hε y hy) y]
    exact ⟨ε y • v, ⟨v, hv, rfl⟩, rfl⟩

/-- The regular-closed part of the argument only needs inflation itself to be closed. -/
theorem isRegularClosed_inflation_of_isClosed (ε : E → ℝ) (B : Set E)
    (hB : IsRegularClosed B) (hε : ∀ y ∈ B, 0 ≤ ε y)
    (hclosed : IsClosed (inflation ε B)) : IsRegularClosed (inflation ε B) := by
  apply subset_antisymm
  · exact closure_minimal interior_subset hclosed
  · intro z hz
    obtain ⟨y, hy, hzball⟩ := (mem_inflation ε B z).mp hz
    change z ∈ Metric.closedBall y (ε y) at hzball
    by_cases hpositive : 0 < ε y
    · rw [← closure_ball y (ne_of_gt hpositive)] at hzball
      exact closure_mono (ball_subset_interior_inflation ε B y hy) hzball
    · have hzero : ε y = 0 := le_antisymm (le_of_not_gt hpositive) (hε y hy)
      have hzy : z = y := by simpa only [hzero, Metric.closedBall_zero, Set.mem_singleton_iff] using hzball
      subst z
      have hyclosure : y ∈ closure (interior B) := by rw [hB]; exact hy
      exact closure_mono (interior_mono (subset_inflation ε B hε)) hyclosure

variable [ProperSpace E]

/-- Compactness uses relative continuity of the radius, not a global continuous extension. -/
theorem isCompact_inflation (ε : E → ℝ) (B : Set E) (hB : IsCompact B)
    (hcontinuous : ContinuousOn ε B) (hε : ∀ y ∈ B, 0 ≤ ε y) :
    IsCompact (inflation ε B) := by
  rw [inflation_eq_image_prod_closedBall ε B hε]
  apply (hB.prod (isCompact_closedBall (0 : E) 1)).image_of_continuousOn
  exact continuous_fst.continuousOn.add
    ((hcontinuous.comp continuous_fst.continuousOn (fun _ hp => hp.1)).smul
      continuous_snd.continuousOn)

theorem isRegularClosed_inflation (ε : E → ℝ) (B : Set E)
    (hBcompact : IsCompact B) (hBregular : IsRegularClosed B)
    (hcontinuous : ContinuousOn ε B) (hε : ∀ y ∈ B, 0 ≤ ε y) :
    IsRegularClosed (inflation ε B) :=
  isRegularClosed_inflation_of_isClosed ε B hBregular hε
    (isCompact_inflation ε B hBcompact hcontinuous hε).isClosed

/-- Every boundary point has a centre whose constituent sphere contains it. -/
theorem exists_mem_sphere_of_mem_frontier_inflation (ε : E → ℝ) (B : Set E)
    (hB : IsCompact B) (hcontinuous : ContinuousOn ε B) (hε : ∀ y ∈ B, 0 ≤ ε y)
    (z : E) (hz : z ∈ frontier (inflation ε B)) :
    ∃ y ∈ B, z ∈ Metric.sphere y (ε y) := by
  obtain ⟨y, hy, hzball⟩ := (mem_inflation ε B z).mp
    ((isCompact_inflation ε B hB hcontinuous hε).isClosed.frontier_subset hz)
  exact ⟨y, hy, le_antisymm hzball (radius_le_dist_of_frontier_inflation ε B z y hz hy)⟩

/-- The final set inclusion in Lemma 3.4 follows from its local contributor statement. -/
theorem frontier_inflation_subset_of_contributors_on_frontier (ε : E → ℝ) (B : Set E)
    (hB : IsCompact B) (hcontinuous : ContinuousOn ε B) (hε : ∀ y ∈ B, 0 ≤ ε y)
    (hcontributor : ∀ z ∈ frontier (inflation ε B), ∀ y ∈ B,
      z ∈ Metric.sphere y (ε y) → y ∈ frontier B) :
    frontier (inflation ε B) ⊆ inflation ε (frontier B) := by
  intro z hz
  obtain ⟨y, hy, hzsphere⟩ :=
    exists_mem_sphere_of_mem_frontier_inflation ε B hB hcontinuous hε z hz
  exact (mem_inflation ε (frontier B) z).mpr
    ⟨y, hcontributor z hz y hy hzsphere, le_of_eq hzsphere⟩

end BoundedUncertainty
