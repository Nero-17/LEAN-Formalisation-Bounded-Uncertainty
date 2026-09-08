import BoundedUncertainty.Basic

/-!
# The union-defined dual construction

Definition 4.13 and the valid factorizations in Lemmas 4.14 and 4.15.
The definitions retain actual membership in a constituent closed ball. No
identification with a weak distance sublevel is made for an arbitrary set.
The factorization is a preimage identity and needs no invertibility hypothesis.
-/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E]

/-- Centers whose variable-radius closed balls contain the specified point. -/
def dualBall (radius : E → ℝ) (x : E) : Set E :=
  {y | dist x y ≤ radius y}

/-- Dual inflation is the actual union of dual balls over the input set. -/
def dualInflation (radius : E → ℝ) (A : Set E) : Set E :=
  ⋃ x ∈ A, dualBall radius x

theorem mem_dualBall (radius : E → ℝ) (x y : E) :
    y ∈ dualBall radius x ↔ x ∈ Metric.closedBall y (radius y) := Iff.rfl

theorem mem_dualInflation (radius : E → ℝ) (A : Set E) (y : E) :
    y ∈ dualInflation radius A ↔ ∃ x ∈ A, dist x y ≤ radius y := by
  simp only [dualInflation, mem_iUnion, dualBall, mem_setOf_eq, exists_prop]

@[simp] theorem dualInflation_empty (radius : E → ℝ) : dualInflation radius ∅ = ∅ := by
  simp only [dualInflation, mem_empty_iff_false, iUnion_of_empty, iUnion_empty]

@[simp] theorem dualInflation_singleton (radius : E → ℝ) (x : E) :
    dualInflation radius {x} = dualBall radius x := by
  simp only [dualInflation, mem_singleton_iff, iUnion_iUnion_eq_left]

theorem dualInflation_mono (radius : E → ℝ) {A B : Set E} (hAB : A ⊆ B) :
    dualInflation radius A ⊆ dualInflation radius B := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_dualInflation radius A y).mp hy
  exact (mem_dualInflation radius B y).mpr ⟨x, hAB hx, hxy⟩

/-- The actual inverse incidence relation of the one-step set-valued point map. -/
def dualPointMap (f : E → E) (radius : E → ℝ) (x : E) : Set E :=
  {y | x ∈ setValuedImage f radius {y}}

/-- The setwise dual map is the union of the actual pointwise incidence sets. -/
def dualSetMap (f : E → E) (radius : E → ℝ) (A : Set E) : Set E :=
  ⋃ x ∈ A, dualPointMap f radius x

/-- Lemma 4.14: the pointwise dual map is the pullback of the dual ball. -/
theorem dualPointMap_eq_preimage (f : E → E) (radius : E → ℝ) (x : E) :
    dualPointMap f radius x = f ⁻¹' dualBall radius x := by
  ext y
  simp only [dualPointMap, mem_setOf_eq, setValuedImage, mem_iUnion,
    mem_singleton_iff, exists_prop, exists_eq_left, mem_preimage, dualBall, Metric.mem_closedBall]

/-- Lemma 4.15's valid setwise factorization, for every input set. -/
theorem dualSetMap_eq_preimage (f : E → E) (radius : E → ℝ) (A : Set E) :
    dualSetMap f radius A = f ⁻¹' dualInflation radius A := by
  ext y
  simp only [dualSetMap, dualInflation, mem_iUnion, dualPointMap_eq_preimage, mem_preimage]

theorem mem_dualSetMap (f : E → E) (radius : E → ℝ) (A : Set E) (y : E) :
    y ∈ dualSetMap f radius A ↔ ∃ x ∈ A, x ∈ setValuedImage f radius {y} := by
  simp only [dualSetMap, dualPointMap, mem_iUnion, mem_setOf_eq, exists_prop]

/-- In the self-bijection case, the pullback is also the image under the inverse map. -/
theorem dualSetMap_equiv_eq_inverse_image (f : E ≃ E) (radius : E → ℝ) (A : Set E) :
    dualSetMap f radius A = f.symm '' dualInflation radius A := by
  rw [dualSetMap_eq_preimage]
  ext y
  constructor
  · intro hy
    exact ⟨f y, hy, f.symm_apply_apply y⟩
  · rintro ⟨z, hz, rfl⟩
    simpa only [mem_preimage, f.apply_symm_apply] using hz

end BoundedUncertainty
