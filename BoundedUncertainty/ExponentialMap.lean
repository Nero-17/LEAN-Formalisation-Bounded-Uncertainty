import BoundedUncertainty.NormalFormula

/-!
# The exponential lift in Definition 3.9 and Proposition 3.10

The parameter `gradient : E → E` records the radius gradient at each centre.
The algebraic results below apply to any such vector field satisfying the
stated contraction bound; identifying it with the derivative of a local
ambient extension is a separate obligation. The radius may vanish.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The displayed exponential lift, with the vector field supplied explicitly. -/
noncomputable def exponentialMap (ε : E → ℝ) (gradient : E → E) (p : E × E) :
    E × E :=
  (p.1 + ε p.1 • normalUpdate (gradient p.1) p.2,
    normalUpdate (gradient p.1) p.2)

theorem exponentialMap_normal_unit (ε : E → ℝ) (gradient : E → E) (y n : E)
    (hgradient : ‖gradient y‖ < 1) (hn : ‖n‖ = 1) :
    ‖(exponentialMap ε gradient (y, n)).2‖ = 1 :=
  norm_normalUpdate (gradient y) n hgradient hn

theorem exponentialMap_position_dist (ε : E → ℝ) (gradient : E → E) (y n : E)
    (hε : 0 ≤ ε y) (hgradient : ‖gradient y‖ < 1) (hn : ‖n‖ = 1) :
    dist (exponentialMap ε gradient (y, n)).1 y = ε y := by
  change dist (y + ε y • normalUpdate (gradient y) n) y = ε y
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hε, norm_normalUpdate (gradient y) n hgradient hn, mul_one]

theorem exponentialMap_position_mem_sphere (ε : E → ℝ) (gradient : E → E) (y n : E)
    (hε : 0 ≤ ε y) (hgradient : ‖gradient y‖ < 1) (hn : ‖n‖ = 1) :
    (exponentialMap ε gradient (y, n)).1 ∈ Metric.sphere y (ε y) :=
  exponentialMap_position_dist ε gradient y n hε hgradient hn

theorem exponentialMap_position_mem_closedBall (ε : E → ℝ) (gradient : E → E)
    (y n : E) (hε : 0 ≤ ε y) (hgradient : ‖gradient y‖ < 1) (hn : ‖n‖ = 1) :
    (exponentialMap ε gradient (y, n)).1 ∈ Metric.closedBall y (ε y) := by
  change dist (exponentialMap ε gradient (y, n)).1 y ≤ ε y
  exact le_of_eq (exponentialMap_position_dist ε gradient y n hε hgradient hn)

theorem exponentialMap_position_mem (ε : E → ℝ) (gradient : E → E)
    (y n : E) {X : Set E} (hε : 0 ≤ ε y) (hgradient : ‖gradient y‖ < 1)
    (hn : ‖n‖ = 1) (hball : Metric.closedBall y (ε y) ⊆ X) :
    (exponentialMap ε gradient (y, n)).1 ∈ X :=
  hball (exponentialMap_position_mem_closedBall ε gradient y n hε hgradient hn)

/-- A zero radius fixes the position; the output normal can still change. -/
theorem exponentialMap_position_of_radius_zero (ε : E → ℝ) (gradient : E → E)
    (y n : E) (hε : ε y = 0) :
    (exponentialMap ε gradient (y, n)).1 = y := by
  simp [exponentialMap, hε]

/-- Proposition 3.10's map from centres and unit normals to positions and unit normals. -/
noncomputable def exponentialBundleMap (X : Set E) (ε : E → ℝ) (gradient : E → E)
    (hgradient : ∀ y ∈ X, ‖gradient y‖ < 1) :
    X × {n : E // ‖n‖ = 1} → E × {n : E // ‖n‖ = 1} :=
  fun p => ((exponentialMap ε gradient (p.1, p.2)).1,
    ⟨(exponentialMap ε gradient (p.1, p.2)).2,
      exponentialMap_normal_unit ε gradient p.1 p.2
        (hgradient p.1 p.1.property) p.2.property⟩)

theorem exponentialBundleMap_position_mem (X : Set E) (ε : E → ℝ)
    (gradient : E → E) (hgradient : ∀ y ∈ X, ‖gradient y‖ < 1)
    (hε : ∀ y ∈ X, 0 ≤ ε y)
    (hball : ∀ y ∈ X, Metric.closedBall y (ε y) ⊆ X)
    (p : X × {n : E // ‖n‖ = 1}) :
    (exponentialBundleMap X ε gradient hgradient p).1 ∈ X :=
  exponentialMap_position_mem ε gradient p.1 p.2
    (hε p.1 p.1.property) (hgradient p.1 p.1.property)
    p.2.property (hball p.1 p.1.property)

/-- Only relative continuity on the centre set is required. -/
theorem continuous_exponentialBundleMap (X : Set E) (ε : E → ℝ)
    (gradient : E → E) (hgradient : ∀ y ∈ X, ‖gradient y‖ < 1)
    (hεcontinuous : ContinuousOn ε X) (hgradientcontinuous : ContinuousOn gradient X) :
    Continuous (exponentialBundleMap X ε gradient hgradient) := by
  have hnormal : Continuous (fun p : X × {n : E // ‖n‖ = 1} =>
      normalUpdate (gradient p.1) p.2) :=
    continuous_normalUpdate.comp
      ((hgradientcontinuous.restrict.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hposition : Continuous (fun p : X × {n : E // ‖n‖ = 1} =>
      (p.1 : E) + ε p.1 • normalUpdate (gradient p.1) p.2) :=
    (continuous_subtype_val.comp continuous_fst).add
      ((hεcontinuous.restrict.comp continuous_fst).smul hnormal)
  exact hposition.prodMk (hnormal.subtype_mk _)

end BoundedUncertainty
