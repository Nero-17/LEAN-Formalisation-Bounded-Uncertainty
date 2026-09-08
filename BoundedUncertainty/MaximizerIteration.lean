import BoundedUncertainty.MaximizerTransport
import BoundedUncertainty.SetValuedIterates

/-!
The auxiliary maximization induction in Theorem 4.10. Local maximizers suffice.
Only the initial frontier is smooth; no intermediate boundary data are inputs.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- Every nonzero maximizing gradient at level n is an n-fold transported initial normal. -/
theorem SetValuedSystem.normalized_gradient_mem_iterated_boundaryNormalInput
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hclosed : IsClosed A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (n : ℕ) (x : system.domain)
    (hx : (x : E) ∈ setValuedIterate system.map system.radius n A)
    (G : E → ℝ) (gradient : E) (hG : ContDiffAt ℝ 1 G (x : E))
    (hgradient : HasGradientAt G gradient (x : E)) (hnonzero : gradient ≠ 0)
    (hmax : IsLocalMaxOn G (setValuedIterate system.map system.radius n A) (x : E)) :
    (x, ⟨‖gradient‖⁻¹ • gradient, norm_smul_inv_norm hnonzero⟩) ∈
      (system.boundaryMap hcontraction)^[n] ''
        range (system.boundaryNormalInput A hA source) := by
  induction n generalizing x G gradient with
  | zero =>
    have hxfrontier : (x : E) ∈ frontier A := by
      rw [hclosed.frontier_eq]
      exact ⟨hx, not_mem_interior_of_isLocalMaxOn_hasGradientAt hmax hgradient hnonzero⟩
    refine ⟨system.boundaryNormalInput A hA source ⟨x, hxfrontier⟩,
      ⟨⟨x, hxfrontier⟩, rfl⟩, ?_⟩
    simp only [Function.iterate_zero, id_eq]
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      exact ((source ⟨x, hxfrontier⟩).normal_eq_normalized_gradient_of_isLocalMaxOn
        G gradient hgradient hnonzero hmax).symm
  | succ n ih =>
    obtain ⟨a, ha, pullback, pullbackGradient, hpullback, hsmooth, hmaximum,
      hderivative, htransport⟩ := system.exists_predecessor_local_maximizer hcontraction
        (setValuedIterate system.map system.radius n A)
        (system.setValuedIterate_subset_domain A hA n) x hx
        G gradient hG hgradient hnonzero hmax
    obtain ⟨initial, hinitial, hiterate⟩ :=
      ih a ha pullback pullbackGradient hsmooth hderivative hpullback hmaximum
    refine ⟨initial, hinitial, ?_⟩
    rw [Function.iterate_succ_apply', hiterate]
    exact htransport

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The maximization statement under the manuscript's original frontier hypothesis. -/
theorem SetValuedSystem.normalized_gradient_mem_iterated_normals_of_frontierGraph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (n : ℕ) (x : system.domain)
    (hx : (x : E) ∈ setValuedIterate system.map system.radius n A)
    (G : E → ℝ) (gradient : E) (hG : ContDiffAt ℝ 1 G (x : E))
    (hgradient : HasGradientAt G gradient (x : E)) (hnonzero : gradient ≠ 0)
    (hmax : IsLocalMaxOn G (setValuedIterate system.map system.radius n A) (x : E)) :
    (x, ⟨‖gradient‖⁻¹ • gradient, norm_smul_inv_norm hnonzero⟩) ∈
      (system.boundaryMap hcontraction)^[n] '' range
        (system.boundaryNormalInput A hA (fun x => (source x).toC1BoundaryAt hregular)) :=
  system.normalized_gradient_mem_iterated_boundaryNormalInput hcontraction
    A hA hregular.isClosed (fun x => (source x).toC1BoundaryAt hregular)
    n x hx G gradient hG hgradient hnonzero hmax

end BoundedUncertainty
