import BoundedUncertainty.SIRSGeometry
import BoundedUncertainty.Section3Interfaces
import BoundedUncertainty.C1FrontierGraph
import BoundedUncertainty.ConstantRadius
import BoundedUncertainty.BoundaryHomeomorph

/-! A compact regular closed invariant set need not have a C1 frontier.
The identity system with zero radius preserves the triangle, whose vertex
cannot have a C1 boundary chart. This is an actual system, not a stipulated
failure of smoothness. -/

namespace BoundedUncertainty

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def C1BoundaryAt.linearHalfspace (normal : E) (hunit : ‖normal‖ = 1) :
    C1BoundaryAt {x : E | inner ℝ normal x ≤ 0} 0 where
  neighborhood := univ
  isOpen_neighborhood := isOpen_univ
  mem_neighborhood := mem_univ 0
  defining := fun x => inner ℝ normal x
  contDiffOn_defining := (InnerProductSpace.toDual ℝ E normal).contDiff.contDiffOn
  defining_eq_zero := by simp
  mem_iff := fun _ _ => Iff.rfl
  normal := normal
  normal_unit := hunit
  hasGradientAt_defining := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (InnerProductSpace.toDual ℝ E normal).hasFDerivAt

theorem not_nonempty_C1BoundaryAt_sirsSimplex_vertex :
    ¬ Nonempty (C1BoundaryAt sirsSimplex (0 : EuclideanSpace ℝ (Fin 2))) := by
  rintro ⟨boundary⟩
  have hfirst := boundary.normal_eq_of_subset
    (C1BoundaryAt.linearHalfspace (-EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (by simp))
    (by
      intro p hp
      change inner ℝ (-EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) p ≤ 0
      simpa [EuclideanSpace.inner_single_left] using neg_nonpos.mpr hp.1)
  have hsecond := boundary.normal_eq_of_subset
    (C1BoundaryAt.linearHalfspace (-EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (by simp))
    (by
      intro p hp
      change inner ℝ (-EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) p ≤ 0
      simpa [EuclideanSpace.inner_single_left] using neg_nonpos.mpr hp.2.1)
  have hcontradiction := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0)
    (hfirst.symm.trans hsecond)
  norm_num [C1BoundaryAt.linearHalfspace, EuclideanSpace.single_apply] at hcontradiction

theorem not_nonempty_C1FrontierGraphAt_sirsSimplex_vertex
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ¬ Nonempty (C1FrontierGraphAt (F := F) sirsSimplex (0 : EuclideanSpace ℝ (Fin 2))) := by
  rintro ⟨chart⟩
  exact not_nonempty_C1BoundaryAt_sirsSimplex_vertex
    ⟨chart.toC1BoundaryAt isRegularClosed_sirsSimplex⟩

noncomputable def identityZeroRadiusSystem : SetValuedSystem (E := EuclideanSpace ℝ (Fin 2)) 1 1 where
  dimension_at_least_two := by simp
  domain := univ
  regular_closed := by simp [IsRegularClosed]
  map := id
  radius := fun _ => 0
  radius_bound := 1
  radius_bound_pos := zero_lt_one
  radius_order_pos := le_rfl
  map_order_pos := le_rfl
  map_into_domain := mapsTo_univ _ _
  diffeomorphism := ambientDiffeomorphismOn_id 1 univ
  radius_extension := hasLocalExtensionOn_of_contDiff 1 univ (fun _ => 0) contDiff_const
  radius_nonneg := fun _ _ => le_rfl
  radius_le_bound := fun _ _ => zero_le_one
  ball_into_domain := fun _ _ => subset_univ _

theorem identityZeroRadiusSystem_isContraction : identityZeroRadiusSystem.IsContraction :=
  identityZeroRadiusSystem.isContraction_of_constant_radius 0 (fun _ _ => rfl)

/-- Its boundary map is nevertheless a homeomorphism of the entire unit-normal bundle. -/
noncomputable def identityZeroRadiusBoundaryHomeomorph :
    (identityZeroRadiusSystem.domain × {n : EuclideanSpace ℝ (Fin 2) // ‖n‖ = 1}) ≃ₜ
      (identityZeroRadiusSystem.domain × {n : EuclideanSpace ℝ (Fin 2) // ‖n‖ = 1}) :=
  identityZeroRadiusSystem.boundaryHomeomorphSelf identityZeroRadiusSystem_isContraction
    (by simp [identityZeroRadiusSystem])

theorem identityZeroRadiusBoundaryHomeomorph_apply
    (p : identityZeroRadiusSystem.domain × {n : EuclideanSpace ℝ (Fin 2) // ‖n‖ = 1}) :
    identityZeroRadiusBoundaryHomeomorph p =
      identityZeroRadiusSystem.boundaryMap identityZeroRadiusSystem_isContraction p := rfl

theorem identity_zero_radius_setValuedImage (A : Set (EuclideanSpace ℝ (Fin 2))) :
    setValuedImage identityZeroRadiusSystem.map identityZeroRadiusSystem.radius A = A := by
  ext z
  simp [setValuedImage, identityZeroRadiusSystem, Metric.closedBall_zero]

/-- A certified compact regular closed invariant set with no C1 frontier at its vertex. -/
theorem exists_nonsmooth_compact_regular_closed_invariant :
    ∃ A : Set (EuclideanSpace ℝ (Fin 2)), IsCompact A ∧ IsRegularClosed A ∧
      setValuedImage identityZeroRadiusSystem.map identityZeroRadiusSystem.radius A = A ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ frontier A ∧
      ¬ Nonempty (C1BoundaryAt A (0 : EuclideanSpace ℝ (Fin 2))) := by
  refine ⟨sirsSimplex, isCompact_sirsSimplex, isRegularClosed_sirsSimplex,
    identity_zero_radius_setValuedImage sirsSimplex, ?_,
    not_nonempty_C1BoundaryAt_sirsSimplex_vertex⟩
  rw [isClosed_sirsSimplex.frontier_eq]
  refine ⟨by simp [sirsSimplex], ?_⟩
  rw [mem_interior_sirsSimplex]
  simp

end BoundedUncertainty
