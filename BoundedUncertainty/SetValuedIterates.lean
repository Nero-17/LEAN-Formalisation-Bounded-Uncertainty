import BoundedUncertainty.ForwardNormalBundle

/-! Domain, compactness, and regular-closedness facts for all finite set-valued iterates. -/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.setValuedIterate_subset_domain
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (n : ℕ) : setValuedIterate system.map system.radius n A ⊆ system.domain := by
  induction n with
  | zero => exact hA
  | succ n inductionHypothesis => exact system.image_subset_domain inductionHypothesis

omit [CompleteSpace E] in
theorem SetValuedSystem.isCompact_setValuedImage
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) : IsCompact (setValuedImage system.map system.radius A) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  have himage : system.map '' A ⊆ system.domain := by
    rintro y ⟨x, hx, rfl⟩
    exact system.map_into_domain (hA hx)
  rw [setValuedImage_eq_inflation]
  exact isCompact_inflation system.radius (system.map '' A)
    (system.diffeomorphism.isCompact_image hA hcompact)
    (system.radius_extension.continuousOn.mono himage)
    (fun y hy => system.radius_nonneg y (himage hy))

omit [CompleteSpace E] in
theorem SetValuedSystem.isCompact_setValuedIterate
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) (n : ℕ) :
    IsCompact (setValuedIterate system.map system.radius n A) := by
  induction n with
  | zero => exact hcompact
  | succ n inductionHypothesis =>
      exact system.isCompact_setValuedImage _
        (system.setValuedIterate_subset_domain A hA n) inductionHypothesis

theorem SetValuedSystem.isRegularClosed_setValuedIterate
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) (hregular : IsRegularClosed A) (n : ℕ) :
    IsRegularClosed (setValuedIterate system.map system.radius n A) := by
  induction n with
  | zero => exact hregular
  | succ n inductionHypothesis =>
      exact system.isRegularClosed_setValuedImage _
        (system.setValuedIterate_subset_domain A hA n)
        (system.isCompact_setValuedIterate A hA hcompact n) inductionHypothesis

omit [CompleteSpace E] in
theorem SetValuedSystem.setValuedImage_nonempty
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hnonempty : A.Nonempty) : (setValuedImage system.map system.radius A).Nonempty := by
  obtain ⟨x, hx⟩ := hnonempty
  refine ⟨system.map x, mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, ?_⟩⟩⟩
  exact Metric.mem_closedBall_self (system.radius_nonneg _ (system.map_into_domain (hA hx)))

omit [CompleteSpace E] in
theorem SetValuedSystem.setValuedIterate_nonempty
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hnonempty : A.Nonempty) (n : ℕ) :
    (setValuedIterate system.map system.radius n A).Nonempty := by
  induction n with
  | zero => exact hnonempty
  | succ n inductionHypothesis =>
      exact system.setValuedImage_nonempty _
        (system.setValuedIterate_subset_domain A hA n) inductionHypothesis

end BoundedUncertainty
