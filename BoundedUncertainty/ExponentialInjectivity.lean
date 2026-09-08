import BoundedUncertainty.RayMonotonicity
import Mathlib.Tactic.Abel

/-!
# Injectivity of the exponential lift on admissible centres

This is the injectivity step of Theorem 3.14. The proof only uses containment
of the two constituent closed balls in the state space. It therefore applies
to any admissible centre set, without convexity, closedness of that centre
set, or strict positivity of the radius.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The part of a unit-speed ray between its tip and a centre stays in that centre's ball. -/
theorem ray_mem_closedBall (z u : E) (R q : ℝ) (hu : ‖u‖ = 1)
    (hqnonneg : 0 ≤ q) (hq : q ≤ R) :
    z - q • u ∈ Metric.closedBall (z - R • u) R := by
  change dist (z - q • u) (z - R • u) ≤ R
  have hsub : (z - q • u) - (z - R • u) = (R - q) • u := by
    rw [sub_smul]
    abel
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hq), hu, mul_one]
  exact sub_le_self R hqnonneg

theorem exponentialMap_position_sub_radius_smul_normal (ε : E → ℝ)
    (gradient : E → E) (y n : E) :
    (exponentialMap ε gradient (y, n)).1 -
      ε y • (exponentialMap ε gradient (y, n)).2 = y := by
  simp only [exponentialMap, add_sub_cancel_right]

variable [CompleteSpace E] {r s : ℕ}

/-- A larger-radius centre cannot give a second root on the same admissible ray. -/
theorem SetValuedSystem.radius_ray_root_not_lt
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (y₁ y₂ z u : E) (hy₁ : y₁ ∈ system.domain)
    (hball₂ : Metric.closedBall y₂ (system.radius y₂) ⊆ system.domain)
    (hu : ‖u‖ = 1)
    (hroot₁ : z - system.radius y₁ • u = y₁)
    (hroot₂ : z - system.radius y₂ • u = y₂) :
    ¬ system.radius y₁ < system.radius y₂ := by
  intro hlt
  have hray : ∀ q ∈ Set.Icc (system.radius y₁) (system.radius y₂),
      z - q • u ∈ system.domain := by
    intro q hq
    apply hball₂
    have hmem := ray_mem_closedBall z u (system.radius y₂) q hu
      ((system.radius_nonneg y₁ hy₁).trans hq.1) hq.2
    rw [hroot₂] at hmem
    exact hmem
  have hstrict := system.strictMonoOn_radius_ray hcontraction z u hu
    (system.radius y₁) (system.radius y₂) hray
  have hltzero := hstrict ⟨le_rfl, le_of_lt hlt⟩ ⟨le_of_lt hlt, le_rfl⟩ hlt
  dsimp only at hltzero
  rw [hroot₁, hroot₂, sub_self, sub_self] at hltzero
  exact (lt_irrefl (0 : ℝ)) hltzero

theorem SetValuedSystem.radius_eq_of_ray_roots
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (y₁ y₂ z u : E) (hy₁ : y₁ ∈ system.domain) (hy₂ : y₂ ∈ system.domain)
    (hball₁ : Metric.closedBall y₁ (system.radius y₁) ⊆ system.domain)
    (hball₂ : Metric.closedBall y₂ (system.radius y₂) ⊆ system.domain)
    (hu : ‖u‖ = 1)
    (hroot₁ : z - system.radius y₁ • u = y₁)
    (hroot₂ : z - system.radius y₂ • u = y₂) :
    system.radius y₁ = system.radius y₂ := by
  apply le_antisymm
  · exact le_of_not_gt
      (system.radius_ray_root_not_lt hcontraction y₂ y₁ z u hy₂ hball₁ hu hroot₂ hroot₁)
  · exact le_of_not_gt
      (system.radius_ray_root_not_lt hcontraction y₁ y₂ z u hy₁ hball₂ hu hroot₁ hroot₂)

/-- Equality of outputs determines both admissible centres and both input normals. -/
theorem SetValuedSystem.exponentialMap_inj_of_ball_subset
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (y₁ y₂ n₁ n₂ : E) (hy₁ : y₁ ∈ system.domain) (hy₂ : y₂ ∈ system.domain)
    (hball₁ : Metric.closedBall y₁ (system.radius y₁) ⊆ system.domain)
    (hball₂ : Metric.closedBall y₂ (system.radius y₂) ⊆ system.domain)
    (hn₁ : ‖n₁‖ = 1) (hn₂ : ‖n₂‖ = 1)
    (heq : exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁) =
      exponentialMap system.radius system.radiusGradientOnAmbient (y₂, n₂)) :
    (y₁, n₁) = (y₂, n₂) := by
  have hroot₁ := exponentialMap_position_sub_radius_smul_normal
    system.radius system.radiusGradientOnAmbient y₁ n₁
  have hroot₂ :
      (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).1 -
        system.radius y₂ •
          (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).2 = y₂ := by
    rw [heq]
    exact exponentialMap_position_sub_radius_smul_normal
      system.radius system.radiusGradientOnAmbient y₂ n₂
  have hradius := system.radius_eq_of_ray_roots hcontraction y₁ y₂
    (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).1
    (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).2
    hy₁ hy₂ hball₁ hball₂
    (exponentialMap_normal_unit system.radius system.radiusGradientOnAmbient y₁ n₁
      (hcontraction.norm_radiusGradientOnAmbient y₁ hy₁) hn₁)
    hroot₁ hroot₂
  have hcentres : y₁ = y₂ := by
    calc
      y₁ = (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).1 -
          system.radius y₁ •
            (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).2 := hroot₁.symm
      _ = (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).1 -
          system.radius y₂ •
            (exponentialMap system.radius system.radiusGradientOnAmbient (y₁, n₁)).2 := by
        rw [hradius]
      _ = y₂ := hroot₂
  subst y₂
  apply Prod.ext
  · rfl
  · exact normalUpdate_inj (system.radiusGradientOnAmbient y₁) n₁ n₂
      (hcontraction.norm_radiusGradientOnAmbient y₁ hy₁) hn₁ hn₂
      (congrArg Prod.snd heq)

/-- The centre set can be any subset whose constituent balls remain in the domain. -/
theorem SetValuedSystem.exponentialMap_injOn_admissible_centres
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (centres : Set E) (hcentres : centres ⊆ system.domain)
    (hballs : ∀ y ∈ centres, Metric.closedBall y (system.radius y) ⊆ system.domain) :
    Set.InjOn (exponentialMap system.radius system.radiusGradientOnAmbient)
      (centres ×ˢ {n : E | ‖n‖ = 1}) := by
  rintro ⟨y₁, n₁⟩ ⟨hy₁, hn₁⟩ ⟨y₂, n₂⟩ ⟨hy₂, hn₂⟩ heq
  exact system.exponentialMap_inj_of_ball_subset hcontraction y₁ y₂ n₁ n₂
    (hcentres hy₁) (hcentres hy₂) (hballs y₁ hy₁) (hballs y₂ hy₂) hn₁ hn₂ heq

/-- The injectivity assertion for the exponential lift used in Theorem 3.14. -/
theorem SetValuedSystem.exponentialMap_injOn_image
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    Set.InjOn (exponentialMap system.radius system.radiusGradientOnAmbient)
      ((system.map '' system.domain) ×ˢ {n : E | ‖n‖ = 1}) := by
  apply system.exponentialMap_injOn_admissible_centres hcontraction
  · rintro y ⟨x, hx, rfl⟩
    exact system.map_into_domain hx
  · rintro y ⟨x, hx, rfl⟩
    exact system.ball_into_domain x hx

theorem SetValuedSystem.exponentialLift_injOn_admissible_centres
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (centres : Set E) (hcentres : centres ⊆ system.domain)
    (hballs : ∀ y ∈ centres, Metric.closedBall y (system.radius y) ⊆ system.domain) :
    Set.InjOn (system.exponentialLift hcontraction)
      {p : system.domain × {n : E // ‖n‖ = 1} |
        (p.1 : E) ∈ centres} := by
  intro p hp q hq heq
  change (p.1 : E) ∈ centres at hp
  change (q.1 : E) ∈ centres at hq
  have hraw :
      exponentialMap system.radius system.radiusGradientOnAmbient ((p.1 : E), (p.2 : E)) =
        exponentialMap system.radius system.radiusGradientOnAmbient ((q.1 : E), (q.2 : E)) := by
    apply Prod.ext
    · exact congrArg (fun output : E × {n : E // ‖n‖ = 1} => output.1) heq
    · exact congrArg (fun output : E × {n : E // ‖n‖ = 1} => (output.2 : E)) heq
  have hpairs : ((p.1 : E), (p.2 : E)) = ((q.1 : E), (q.2 : E)) := by
    apply system.exponentialMap_injOn_admissible_centres hcontraction centres hcentres hballs
    · exact ⟨hp, p.2.property⟩
    · exact ⟨hq, q.2.property⟩
    · exact hraw
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hpairs)
  · exact Subtype.ext (congrArg Prod.snd hpairs)

theorem SetValuedSystem.exponentialLift_injOn_image
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction) :
    Set.InjOn (system.exponentialLift hcontraction)
      {p : system.domain × {n : E // ‖n‖ = 1} |
        (p.1 : E) ∈ system.map '' system.domain} := by
  apply system.exponentialLift_injOn_admissible_centres hcontraction
  · rintro y ⟨x, hx, rfl⟩
    exact system.map_into_domain hx
  · rintro y ⟨x, hx, rfl⟩
    exact system.ball_into_domain x hx

end BoundedUncertainty
