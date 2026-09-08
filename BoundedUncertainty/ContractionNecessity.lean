import BoundedUncertainty.BoundaryMap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Injectivity of the candidate formula forces contraction

The candidate formulas in this file are the ambient, contraction-free formulas.
In dimension at least two, a gradient of norm at least one makes two opposite
orthogonal unit normals have the same output. Lean's real square root is zero
on nonpositive inputs, so this obstruction also handles a negative radicand
without assuming that the candidate already maps into the unit sphere.
-/

namespace BoundedUncertainty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonzero vector has an orthogonal unit vector in dimension at least two. -/
theorem exists_unit_orthogonal_of_two_le_finrank
    (hdimension : 2 ≤ Module.finrank ℝ E) (gradient : E) (hgradient : gradient ≠ 0) :
    ∃ n : E, ‖n‖ = 1 ∧ inner ℝ n gradient = 0 := by
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  have hdimensionSum := (Submodule.span ℝ {gradient}).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hgradient] at hdimensionSum
  have horthogonalDimension :
      0 < Module.finrank ℝ (Submodule.span ℝ {gradient})ᗮ := by omega
  letI : Nontrivial (Submodule.span ℝ {gradient})ᗮ :=
    Module.nontrivial_of_finrank_pos horthogonalDimension
  obtain ⟨v, hv⟩ := exists_ne (0 : (Submodule.span ℝ {gradient})ᗮ)
  have hvnonzero : (v : E) ≠ 0 := fun h => hv (Subtype.ext h)
  have hvorthogonal : inner ℝ (v : E) gradient = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
  refine ⟨‖(v : E)‖⁻¹ • (v : E), norm_smul_inv_norm hvnonzero, ?_⟩
  rw [real_inner_smul_left, hvorthogonal, mul_zero]

/-- Orthogonal inputs collapse to minus the gradient when its norm is at least one. -/
theorem normalUpdate_of_orthogonal_of_one_le_norm (gradient n : E)
    (hgradient : 1 ≤ ‖gradient‖) (horthogonal : inner ℝ n gradient = 0) :
    normalUpdate gradient n = -gradient := by
  have hradicand : (0 : ℝ) ^ 2 - ‖gradient‖ ^ 2 + 1 ≤ 0 := by
    nlinarith [norm_nonneg gradient]
  simp only [normalUpdate, horthogonal, Real.sqrt_eq_zero_of_nonpos hradicand,
    zero_add, zero_smul, zero_sub]

/-- On the unit sphere, injectivity of the raw normal formula already forces
strict contraction. No unit-output hypothesis is required. -/
theorem norm_lt_one_of_normalUpdate_injOn
    (hdimension : 2 ≤ Module.finrank ℝ E) (gradient : E)
    (hinjective : Set.InjOn (normalUpdate gradient) {n : E | ‖n‖ = 1}) :
    ‖gradient‖ < 1 := by
  apply lt_of_not_ge
  intro hgradient
  have hgradientNonzero : gradient ≠ 0 := by
    intro hzero
    norm_num [hzero] at hgradient
  obtain ⟨n, hn, horthogonal⟩ :=
    exists_unit_orthogonal_of_two_le_finrank hdimension gradient hgradientNonzero
  have hnegativeOrthogonal : inner ℝ (-n) gradient = 0 := by
    rw [inner_neg_left, horthogonal, neg_zero]
  have hcollision : normalUpdate gradient n = normalUpdate gradient (-n) := by
    rw [normalUpdate_of_orthogonal_of_one_le_norm gradient n hgradient horthogonal,
      normalUpdate_of_orthogonal_of_one_le_norm gradient (-n) hgradient hnegativeOrthogonal]
  have hopposite : n = -n := hinjective hn
    (by simpa only [Set.mem_setOf_eq, norm_neg] using hn) hcollision
  have hinner := congrArg (fun v : E => inner ℝ n v) hopposite
  norm_num [inner_neg_right, real_inner_self_eq_norm_sq, hn] at hinner

variable [CompleteSpace E] {r s : ℕ}

/-- The contraction-free exponential formula cannot be injective on the full
domain bundle unless the genuine radius gradient is pointwise strictly bounded
by one. This is the converse input needed for Theorem 3.17. -/
theorem SetValuedSystem.isContraction_of_exponentialMap_injOn
    (system : SetValuedSystem (E := E) r s)
    (hinjective : Set.InjOn (exponentialMap system.radius system.radiusGradientOnAmbient)
      (system.domain ×ˢ {n : E | ‖n‖ = 1})) : system.IsContraction := by
  intro y
  apply norm_lt_one_of_normalUpdate_injOn system.dimension_at_least_two (system.radiusGradient y)
  intro n₁ hn₁ n₂ hn₂ hnormal
  have houtputs :
      exponentialMap system.radius system.radiusGradientOnAmbient ((y : E), n₁) =
        exponentialMap system.radius system.radiusGradientOnAmbient ((y : E), n₂) := by
    simp only [exponentialMap, system.radiusGradientOnAmbient_apply y, hnormal]
  exact congrArg Prod.snd (hinjective ⟨y.property, hn₁⟩ ⟨y.property, hn₂⟩ houtputs)

end BoundedUncertainty
