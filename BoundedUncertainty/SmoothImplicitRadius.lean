import BoundedUncertainty.ImplicitRadius

/-!
# One smooth implicit-radius branch on a fixed open neighborhood

First fix a C1 branch and an open neighborhood where its equation holds and
the scalar partial derivative stays nonzero. At every point of this same
neighborhood, finite-order implicit functions agree locally with that fixed
branch by uniqueness. The fixed branch is therefore C-infinity on the whole
neighborhood. No common neighborhood is extracted from `ContDiffAt infinity`.
-/

namespace BoundedUncertainty

open Set Filter Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_smooth_radiusImplicitSolution
    (ε : E → ℝ) (U : Set E) (hU : IsOpen U) (hε : ContDiffOn ℝ ∞ ε U)
    (y u : E) (hy : y ∈ U) (Dε : E →L[ℝ] ℝ)
    (hderivative : HasFDerivAt ε Dε y) (hnonzero : 1 + Dε u ≠ 0) :
    ∃ solution : E × E → ℝ, ∃ V : Set (E × E),
      IsOpen V ∧ (y + ε y • u, u) ∈ V ∧ ContDiffOn ℝ ∞ solution V ∧
      solution (y + ε y • u, u) = ε y ∧
      (∀ p ∈ V, radiusImplicitEquation ε (p, solution p) = 0) ∧
      (∀ᶠ p in 𝓝 ((y + ε y • u, u), ε y),
        radiusImplicitEquation ε p = 0 → solution p.1 = p.2) := by
  obtain ⟨solution, hsolution, hsolutionValue, hequation, hunique⟩ :=
    exists_contDiffAt_radiusImplicitSolution ε y u Dε (by decide : 1 ≤ 1)
      ((hε.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffAt (hU.mem_nhds hy))
      hderivative hnonzero
  have hcentreValue : (y + ε y • u) - solution (y + ε y • u, u) • u = y := by
    rw [hsolutionValue, add_sub_cancel_right]
  have hcentreContinuous : ContinuousAt
      (fun p : E × E => p.1 - solution p • p.2) (y + ε y • u, u) :=
    continuousAt_fst.sub (hsolution.continuousAt.smul continuousAt_snd)
  have hcentreU : ∀ᶠ p in 𝓝 (y + ε y • u, u), p.1 - solution p • p.2 ∈ U :=
    hcentreContinuous (by simpa only [hcentreValue] using hU.mem_nhds hy)
  have hDcontinuous : ContinuousAt (fderiv ℝ ε) y :=
    (hε.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds hy)
  have hpartialContinuous : ContinuousAt
      (fun p : E × E => 1 + fderiv ℝ ε (p.1 - solution p • p.2) p.2)
      (y + ε y • u, u) :=
    continuousAt_const.add
      ((hDcontinuous.comp_of_eq hcentreContinuous hcentreValue).clm_apply continuousAt_snd)
  have hpartialNonzero : ∀ᶠ p in 𝓝 (y + ε y • u, u),
      1 + fderiv ℝ ε (p.1 - solution p • p.2) p.2 ≠ 0 :=
    hpartialContinuous (isOpen_compl_singleton.mem_nhds (by
      simpa only [hcentreValue, hderivative.fderiv] using hnonzero))
  obtain ⟨W, hWnhds, hWC1⟩ := hsolution.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVsubset, hVopen, hbaseV⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem (inter_mem hWnhds hequation) hcentreU) hpartialNonzero)
  refine ⟨solution, V, hVopen, hbaseV, ?_, hsolutionValue,
    fun p hp => (hVsubset hp).1.1.2, hunique⟩
  have hsolutionC1 : ContDiffOn ℝ 1 solution V :=
    hWC1.mono (fun p hp => (hVsubset hp).1.1.1)
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_infty.mpr
  intro order
  have hpEquation : solution p = ε (p.1 - solution p • p.2) :=
    sub_eq_zero.mp ((hVsubset hp).1.1.2)
  have hpCentre : p.1 - solution p • p.2 + ε (p.1 - solution p • p.2) • p.2 = p.1 := by
    rw [← hpEquation, sub_add_cancel]
  have hεAt : ContDiffAt ℝ (order + 1 : ℕ) ε (p.1 - solution p • p.2) :=
    (hε.of_le (WithTop.coe_le_coe.mpr
      (le_top : ((order + 1 : ℕ) : ℕ∞) ≤ ⊤))).contDiffAt (hU.mem_nhds (hVsubset hp).1.2)
  obtain ⟨localSolution, hlocalSmooth, _, _, hlocalUnique⟩ :=
    exists_contDiffAt_radiusImplicitSolution ε (p.1 - solution p • p.2) p.2
      (fderiv ℝ ε (p.1 - solution p • p.2)) (by omega) hεAt
      (hεAt.differentiableAt (by exact_mod_cast (Nat.succ_ne_zero order))).hasFDerivAt
      (hVsubset hp).2
  rw [hpCentre, Prod.eta] at hlocalSmooth hlocalUnique
  rw [← hpEquation] at hlocalUnique
  have hlocalEq : ∀ᶠ q in 𝓝 p, localSolution q = solution q := by
    have hpair : ContinuousAt (fun q : E × E => (q, solution q)) p :=
      continuousAt_id.prodMk (hsolutionC1.contDiffAt (hVopen.mem_nhds hp)).continuousAt
    filter_upwards [hpair hlocalUnique, hVopen.mem_nhds hp] with q hqUnique hqV
    exact hqUnique ((hVsubset hqV).1.1.2)
  exact (hlocalSmooth.congr_of_eventuallyEq (Filter.EventuallyEq.symm hlocalEq)).of_le
    (by exact_mod_cast (Nat.le_succ order))

end BoundedUncertainty
