import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Nearest points of a nonempty compact set and continuity at a point where the
nearest point is unique. No convexity or uniqueness in a neighborhood is used.
The compact gap argument controls every nearby nearest point simultaneously.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [MetricSpace E]

/-- A nearest point selected using actual compact distance attainment. -/
noncomputable def compactNearestPoint (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y : E) : E :=
  (hcompact.exists_infDist_eq_dist hnonempty y).choose

theorem compactNearestPoint_mem (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y : E) : compactNearestPoint A hcompact hnonempty y ∈ A :=
  (hcompact.exists_infDist_eq_dist hnonempty y).choose_spec.1

theorem dist_compactNearestPoint (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y : E) :
    dist y (compactNearestPoint A hcompact hnonempty y) = Metric.infDist y A :=
  (hcompact.exists_infDist_eq_dist hnonempty y).choose_spec.2.symm

/-- Uniqueness at the base point gives a uniform localization of all nearby nearest points. -/
theorem nearestPoint_localization_of_isCompact (A : Set E) (hcompact : IsCompact A)
    (y x : E) (hx : x ∈ A) (hnearest : dist y x = Metric.infDist y A)
    (hunique : ∀ z ∈ A, dist y z = Metric.infDist y A → z = x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : E, dist w y < δ →
      ∀ z ∈ A, dist w z = Metric.infDist w A → dist z x < ε := by
  by_cases hempty : A \ Metric.ball x ε = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro w _ z hz _
    by_contra hnot
    have hmem : z ∈ A \ Metric.ball x ε := ⟨hz, hnot⟩
    simp only [hempty, mem_empty_iff_false] at hmem
  · obtain ⟨a, ha, hminimal⟩ := (hcompact.diff Metric.isOpen_ball).exists_infDist_eq_dist
      (Set.nonempty_iff_ne_empty.mpr hempty) y
    have hbase : dist y x ≤ dist y a :=
      hnearest.trans_le (Metric.infDist_le_dist_of_mem ha.1)
    have hgap : dist y x < dist y a := by
      apply lt_of_le_of_ne hbase
      intro heq
      have hax := hunique a ha.1 (heq.symm.trans hnearest)
      exact ha.2 (hax ▸ Metric.mem_ball_self hε)
    refine ⟨(dist y a - dist y x) / 3, by linarith, ?_⟩
    intro w hw z hz hprojection
    by_contra hnot
    have hzoutside : z ∈ A \ Metric.ball x ε := ⟨hz, hnot⟩
    have hminimalBound : dist y a ≤ dist y z :=
      hminimal.symm.trans_le (Metric.infDist_le_dist_of_mem hzoutside)
    have hnearestBound : dist w z ≤ dist w x :=
      hprojection.trans_le (Metric.infDist_le_dist_of_mem hx)
    have hfirst := dist_triangle y w z
    have hsecond := dist_triangle w y x
    rw [dist_comm y w] at hfirst
    linarith

/-- Any compact nearest-point selector converges to the unique nearest point at the base. -/
theorem tendsto_compactNearestPoint_of_unique (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y x : E) (hx : x ∈ A)
    (hnearest : dist y x = Metric.infDist y A)
    (hunique : ∀ z ∈ A, dist y z = Metric.infDist y A → z = x) :
    Tendsto (compactNearestPoint A hcompact hnonempty) (𝓝 y) (𝓝 x) := by
  apply Metric.tendsto_nhds_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := nearestPoint_localization_of_isCompact A hcompact y x hx
    hnearest hunique ε hε
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  exact hlocal w hw _ (compactNearestPoint_mem A hcompact hnonempty w)
    (dist_compactNearestPoint A hcompact hnonempty w)

theorem continuousAt_compactNearestPoint_of_unique (A : Set E) (hcompact : IsCompact A)
    (hnonempty : A.Nonempty) (y x : E) (hx : x ∈ A)
    (hnearest : dist y x = Metric.infDist y A)
    (hunique : ∀ z ∈ A, dist y z = Metric.infDist y A → z = x) :
    ContinuousAt (compactNearestPoint A hcompact hnonempty) y := by
  have hvalue : compactNearestPoint A hcompact hnonempty y = x :=
    hunique _ (compactNearestPoint_mem A hcompact hnonempty y)
      (dist_compactNearestPoint A hcompact hnonempty y)
  change Tendsto _ (𝓝 y) (𝓝 _)
  rw [hvalue]
  exact tendsto_compactNearestPoint_of_unique A hcompact hnonempty y x hx hnearest hunique

end BoundedUncertainty
