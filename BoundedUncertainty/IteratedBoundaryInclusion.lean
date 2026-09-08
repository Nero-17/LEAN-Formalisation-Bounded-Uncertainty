import BoundedUncertainty.MaximizerIteration
import BoundedUncertainty.BoundaryNormalContinuity
import Mathlib.Topology.Order.Compact

/-!
Theorem 4.10. After the maximization induction, nearest-point maximizers
approximate every frontier point. Compactness of the transported initial
normal bundle closes the argument, without any smooth intermediate frontier.
This is an alternative proof of the manuscript's final inclusion.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A closed set containing all nonzero-gradient maximizers contains the frontier.
Nearest points to exterior points give smooth quadratic maximizers approaching
each frontier point of the compact set. -/
theorem frontier_subset_of_contains_nonzero_gradient_maximizers
    (A P : Set E) (hcompact : IsCompact A) (hclosed : IsClosed P)
    (hcontains : ∀ x ∈ A, ∀ (G : E → ℝ) (gradient : E),
      ContDiffAt ℝ 1 G x → HasGradientAt G gradient x → gradient ≠ 0 →
      IsLocalMaxOn G A x → x ∈ P) : frontier A ⊆ P := by
  intro z hz
  apply hclosed.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro distance hdistance
  have hzclosure : z ∈ closure Aᶜ := by
    rw [closure_compl]
    exact hz.2
  obtain ⟨w, hw, hwnear⟩ := Metric.mem_closure_iff.mp
    hzclosure (distance / 2) (half_pos hdistance)
  obtain ⟨x, hx, hminimum⟩ := hcompact.exists_isMinOn
    ⟨z, hcompact.isClosed.frontier_subset hz⟩
    (continuous_id.dist continuous_const).continuousOn
  have hnonzero : -((2 : ℝ) • (x - w)) ≠ 0 := by
    apply neg_ne_zero.mpr
    apply smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    intro heq
    exact hw (sub_eq_zero.mp heq ▸ hx)
  have hgradient : HasGradientAt (fun t : E => -‖t - w‖ ^ 2)
      (-((2 : ℝ) • (x - w))) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (((hasFDerivAt_id x).sub_const w).norm_sq.neg) using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
  have hmaximum : IsMaxOn (fun t : E => -‖t - w‖ ^ 2) A x := by
    intro t ht
    change -‖t - w‖ ^ 2 ≤ -‖x - w‖ ^ 2
    have hbound : dist x w ≤ dist t w := hminimum ht
    rw [dist_eq_norm, dist_eq_norm] at hbound
    nlinarith [norm_nonneg (x - w), norm_nonneg (t - w)]
  have hlocalMaximum : IsLocalMaxOn (fun t : E => -‖t - w‖ ^ 2) A x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmaximum ht
  refine ⟨x, hcontains x hx (fun t : E => -‖t - w‖ ^ 2) (-((2 : ℝ) • (x - w)))
    (((contDiff_id.sub contDiff_const).norm_sq ℝ).neg.contDiffAt)
    hgradient hnonzero hlocalMaximum, ?_⟩
  have hbound : dist x w ≤ dist z w := hminimum (hcompact.isClosed.frontier_subset hz)
  have htriangle := dist_triangle z w x
  rw [dist_comm w x] at htriangle
  linarith

variable {r s : ℕ}

/-- The projected n-fold transported initial normal bundle is compact. -/
theorem SetValuedSystem.isCompact_projected_iterated_boundaryNormalInput
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x) (n : ℕ) :
    IsCompact ((fun p : system.domain × {v : E // ‖v‖ = 1} => (p.1 : E)) ''
      ((system.boundaryMap hcontraction)^[n] '' range (system.boundaryNormalInput A hA source))) := by
  letI : CompactSpace (frontier A) :=
    isCompact_iff_compactSpace.mp
      (hcompact.of_isClosed_subset isClosed_frontier hcompact.isClosed.frontier_subset)
  have hinput : Continuous (system.boundaryNormalInput A hA source) :=
    (continuous_subtype_val.subtype_mk _).prodMk
      ((continuous_boundaryNormal source).subtype_mk _)
  exact ((isCompact_range hinput).image ((system.continuous_boundaryMap hcontraction).iterate n)).image
    (continuous_subtype_val.comp continuous_fst)

/-- Theorem 4.10 for all n, including zero: no intermediate boundary smoothness is assumed. -/
theorem SetValuedSystem.frontier_setValuedIterate_subset_projected_boundaryNormalInput
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x) (n : ℕ) :
    frontier (setValuedIterate system.map system.radius n A) ⊆
      (fun p : system.domain × {v : E // ‖v‖ = 1} => (p.1 : E)) ''
        ((system.boundaryMap hcontraction)^[n] '' range (system.boundaryNormalInput A hA source)) := by
  apply frontier_subset_of_contains_nonzero_gradient_maximizers _ _
    (system.isCompact_setValuedIterate A hA hcompact n)
    (system.isCompact_projected_iterated_boundaryNormalInput hcontraction A hA hcompact source n).isClosed
  intro x hx G gradient hG hgradient hnonzero hmax
  exact ⟨(⟨x, system.setValuedIterate_subset_domain A hA n hx⟩,
      ⟨‖gradient‖⁻¹ • gradient, norm_smul_inv_norm hnonzero⟩),
    system.normalized_gradient_mem_iterated_boundaryNormalInput hcontraction
      A hA hcompact.isClosed source n
      ⟨x, system.setValuedIterate_subset_domain A hA n hx⟩ hx
      G gradient hG hgradient hnonzero hmax, rfl⟩

/-- Ambient-coordinate iteration agrees at every step with the actual typed beta iteration. -/
theorem SetValuedSystem.iterate_boundaryFormulaOnAmbient_eq_boundaryMap
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (n : ℕ) (p : system.domain × {v : E // ‖v‖ = 1}) :
    system.boundaryFormulaOnAmbient^[n] ((p.1 : E), (p.2 : E)) =
      ((((system.boundaryMap hcontraction)^[n] p).1 : E),
        (((system.boundaryMap hcontraction)^[n] p).2 : E)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', ih,
      system.boundaryFormulaOnAmbient_eq_boundaryMap hcontraction]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The final inclusion with the original unoriented C1-frontier hypotheses. -/
theorem SetValuedSystem.frontier_setValuedIterate_subset_of_frontierGraph
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x) (n : ℕ) :
    frontier (setValuedIterate system.map system.radius n A) ⊆
      (fun p : system.domain × {v : E // ‖v‖ = 1} => (p.1 : E)) ''
        ((system.boundaryMap hcontraction)^[n] '' range
          (system.boundaryNormalInput A hA (fun x => (source x).toC1BoundaryAt hregular))) :=
  system.frontier_setValuedIterate_subset_projected_boundaryNormalInput hcontraction
    A hA hcompact (fun x => (source x).toC1BoundaryAt hregular) n

/-- Theorem 4.10 in the manuscript's ambient projection and outward-normal-bundle notation. -/
theorem SetValuedSystem.frontier_setValuedIterate_subset_projection_iterated_outwardNormalBundle
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x) (n : ℕ) :
    frontier (setValuedIterate system.map system.radius n A) ⊆
      Prod.fst '' (system.boundaryFormulaOnAmbient^[n] '' outwardNormalBundle A hregular source) := by
  intro z hz
  obtain ⟨p, ⟨q, ⟨a, rfl⟩, rfl⟩, hposition⟩ :=
    system.frontier_setValuedIterate_subset_of_frontierGraph hcontraction
      A hA hcompact hregular source n hz
  refine ⟨system.boundaryFormulaOnAmbient^[n] (outwardNormalPair A hregular source a),
    ⟨outwardNormalPair A hregular source a, ⟨a, rfl⟩, rfl⟩, ?_⟩
  change (system.boundaryFormulaOnAmbient^[n]
    (((system.boundaryNormalInput A hA (fun x => (source x).toC1BoundaryAt hregular) a).1 : E),
      ((system.boundaryNormalInput A hA (fun x => (source x).toC1BoundaryAt hregular) a).2 : E))).1 = z
  rw [system.iterate_boundaryFormulaOnAmbient_eq_boundaryMap hcontraction]
  exact hposition

end BoundedUncertainty
