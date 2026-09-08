import BoundedUncertainty.ExponentialInjectivity
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
Closed admissible centre sets and the continuous inverse in Theorem 3.14.
The ambient dimension is finite by the system's existing finrank bound.
The image of the original map is not required to be closed.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {r s : ℕ}

/-- Centres whose whole radius ball stays in the domain, expressed using a fixed unit ball. -/
def SetValuedSystem.admissibleCentres (system : SetValuedSystem (E := E) r s) : Set E :=
  {y | y ∈ system.domain ∧ ∀ v : E, ‖v‖ ≤ 1 →
    y + system.radius y • v ∈ system.domain}

theorem SetValuedSystem.admissibleCentres_subset
    (system : SetValuedSystem (E := E) r s) :
    system.admissibleCentres ⊆ system.domain := fun _ hy => hy.1

theorem SetValuedSystem.isClosed_admissibleCentres
    (system : SetValuedSystem (E := E) r s) : IsClosed system.admissibleCentres := by
  have hclosed : IsClosed {y : system.domain | ∀ v : E, ‖v‖ ≤ 1 →
      (y : E) + system.radius y • v ∈ system.domain} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro _
    exact system.regular_closed.isClosed.preimage
      (continuous_subtype_val.add
        (system.radius_extension.continuousOn.restrict.smul continuous_const))
  have heq : system.admissibleCentres =
      Subtype.val '' {y : system.domain | ∀ v : E, ‖v‖ ≤ 1 →
        (y : E) + system.radius y • v ∈ system.domain} := by
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hy.1⟩, hy.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
  rw [heq]
  exact (IsClosedEmbedding.subtypeVal system.regular_closed.isClosed).isClosedMap _ hclosed

theorem SetValuedSystem.image_subset_admissibleCentres
    (system : SetValuedSystem (E := E) r s) :
    system.map '' system.domain ⊆ system.admissibleCentres := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨system.map_into_domain hx, ?_⟩
  intro v hv
  apply system.ball_into_domain x hx
  change dist (system.map x + system.radius (system.map x) • v) (system.map x) ≤ _
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (system.radius_nonneg _ (system.map_into_domain hx))]
  exact mul_le_of_le_one_right (system.radius_nonneg _ (system.map_into_domain hx)) hv

theorem SetValuedSystem.admissibleCentres_ball_subset
    (system : SetValuedSystem (E := E) r s) (y : E) (hy : y ∈ system.admissibleCentres) :
    Metric.closedBall y (system.radius y) ⊆ system.domain := by
  rw [← affinity_unitClosedBall (system.radius_nonneg y hy.1) y]
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  exact hy.2 v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)

variable [CompleteSpace E]

/-- The exponential lift on an explicitly specified subset of the domain. -/
noncomputable def SetValuedSystem.restrictedExponentialLift
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (centres : Set E) (hcentres : centres ⊆ system.domain) :
    centres × {n : E // ‖n‖ = 1} → E × {n : E // ‖n‖ = 1} :=
  fun p => system.exponentialLift hcontraction (⟨p.1, hcentres p.1.property⟩, p.2)

theorem SetValuedSystem.continuous_restrictedExponentialLift
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (centres : Set E) (hcentres : centres ⊆ system.domain) :
    Continuous (system.restrictedExponentialLift hcontraction centres hcentres) := by
  apply system.continuous_exponentialLift hcontraction |>.comp
  exact (continuous_subtype_val.comp continuous_fst).subtype_mk _ |>.prodMk continuous_snd

theorem SetValuedSystem.isClosedEmbedding_restrictedExponentialLift
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (centres : Set E) (hclosed : IsClosed centres) (hcentres : centres ⊆ system.domain)
    (hballs : ∀ y ∈ centres, Metric.closedBall y (system.radius y) ⊆ system.domain) :
    IsClosedEmbedding (system.restrictedExponentialLift hcontraction centres hcentres) := by
  letI : FiniteDimensional ℝ E := Module.finite_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  have hcontinuous := system.continuous_restrictedExponentialLift hcontraction centres hcentres
  have hinjective : Function.Injective
      (system.restrictedExponentialLift hcontraction centres hcentres) := by
    intro p q hpq
    have heq := system.exponentialLift_injOn_admissible_centres hcontraction centres
      hcentres hballs p.1.property q.1.property hpq
    exact Prod.ext (Subtype.ext (congrArg (fun t => (t.1 : E)) heq))
      (congrArg (fun t : system.domain × {n : E // ‖n‖ = 1} => t.2) heq)
  have hinclusion : IsClosedEmbedding
      (fun p : centres × {n : E // ‖n‖ = 1} => ((p.1 : E), (p.2 : E))) := by
    have hfirst := IsClosedEmbedding.subtypeVal hclosed
    have hsecond : IsClosedEmbedding (Subtype.val : {n : E // ‖n‖ = 1} → E) :=
      IsClosedEmbedding.subtypeVal (isClosed_eq continuous_norm continuous_const)
    exact IsClosedEmbedding.of_continuous_injective_isClosedMap
      (hfirst.continuous.prodMap hsecond.continuous)
      (hfirst.injective.prodMap hsecond.injective)
      (hfirst.isProperMap.prodMap hsecond.isProperMap).isClosedMap
  have hproper : IsProperMap
      (system.restrictedExponentialLift hcontraction centres hcentres) := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hcontinuous, ?_⟩
    intro K hK
    obtain ⟨bound, hbound⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
    apply (hinclusion.isCompact_preimage
      (isCompact_closedBall (0 : E × E) (max (bound + system.radius_bound) 1))).of_isClosed_subset
      (hK.isClosed.preimage hcontinuous)
    intro p hp
    have hposition := hbound _ ⟨system.restrictedExponentialLift hcontraction centres hcentres p,
      hp, rfl⟩
    have hdist : dist (system.restrictedExponentialLift hcontraction centres hcentres p).1
        (p.1 : E) = system.radius p.1 :=
      exponentialMap_position_dist system.radius system.radiusGradientOnAmbient p.1 p.2
        (system.radius_nonneg _ (hcentres p.1.property))
        (hcontraction.norm_radiusGradientOnAmbient _ (hcentres p.1.property)) p.2.property
    have hnorm : ‖(p.1 : E)‖ ≤ bound + system.radius_bound := by
      have htriangle : ‖(p.1 : E)‖ ≤
          ‖(system.restrictedExponentialLift hcontraction centres hcentres p).1‖ +
            system.radius p.1 :=
        norm_le_norm_add_const_of_dist_le (by rw [dist_comm]; exact hdist.le)
      linarith [system.radius_le_bound _ (hcentres p.1.property)]
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def,
      p.2.property]
    exact max_le_max_right 1 hnorm
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap hcontinuous hinjective
    hproper.isClosedMap

end BoundedUncertainty
