import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
The actual product half-space used by defining-function charts is identified
with mathlib's EuclideanHalfSpace model. Dimension positivity is carried by a
local NeZero parameter; this module registers no new instances. The ambient
coordinate equivalence preserves the distinguished first coordinate exactly.
-/

namespace BoundedUncertainty

/-- Join the distinguished real coordinate and the remaining finite coordinates. -/
noncomputable def productEuclideanCoordinates (dimension : ℕ) [NeZero dimension] :
    (ℝ × (Fin (dimension - 1) → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin dimension) := by
  cases dimension with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ n =>
    exact (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm

theorem productEuclideanCoordinates_apply_zero (dimension : ℕ) [NeZero dimension]
    (point : ℝ × (Fin (dimension - 1) → ℝ)) :
    productEuclideanCoordinates dimension point 0 = point.1 := by
  cases dimension with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ n => rfl

theorem productEuclideanCoordinates_symm_fst (dimension : ℕ) [NeZero dimension]
    (point : EuclideanSpace ℝ (Fin dimension)) :
    ((productEuclideanCoordinates dimension).symm point).1 = point 0 := by
  have hcoordinate := productEuclideanCoordinates_apply_zero dimension
    ((productEuclideanCoordinates dimension).symm point)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hcoordinate.symm

/-- The product half-space and mathlib's standard half-space have their actual subtype topologies. -/
noncomputable def halfSpaceModelHomeomorph (dimension : ℕ) [NeZero dimension] :
    {point : ℝ × (Fin (dimension - 1) → ℝ) // 0 ≤ point.1} ≃ₜ
      EuclideanHalfSpace dimension :=
  (productEuclideanCoordinates dimension).toHomeomorph.subtype (by
    intro point
    change 0 ≤ point.1 ↔ 0 ≤ productEuclideanCoordinates dimension point 0
    rw [productEuclideanCoordinates_apply_zero])

theorem halfSpaceModelHomeomorph_coe (dimension : ℕ) [NeZero dimension]
    (point : {point : ℝ × (Fin (dimension - 1) → ℝ) // 0 ≤ point.1}) :
    (halfSpaceModelHomeomorph dimension point).val =
      productEuclideanCoordinates dimension point.val := rfl

theorem halfSpaceModelHomeomorph_apply_zero (dimension : ℕ) [NeZero dimension]
    (point : {point : ℝ × (Fin (dimension - 1) → ℝ) // 0 ≤ point.1}) :
    (halfSpaceModelHomeomorph dimension point).val 0 = point.val.1 :=
  productEuclideanCoordinates_apply_zero dimension point.val

theorem halfSpaceModelHomeomorph_symm_coe (dimension : ℕ) [NeZero dimension]
    (point : EuclideanHalfSpace dimension) :
    ((halfSpaceModelHomeomorph dimension).symm point).val =
      (productEuclideanCoordinates dimension).symm point.val := rfl

theorem halfSpaceModelHomeomorph_symm_fst (dimension : ℕ) [NeZero dimension]
    (point : EuclideanHalfSpace dimension) :
    ((halfSpaceModelHomeomorph dimension).symm point).val.1 = point.val 0 :=
  productEuclideanCoordinates_symm_fst dimension point.val

/-- Model boundary points are precisely those with distinguished product coordinate zero. -/
theorem halfSpaceModelHomeomorph_boundary_iff (dimension : ℕ) [NeZero dimension]
    (point : {point : ℝ × (Fin (dimension - 1) → ℝ) // 0 ≤ point.1}) :
    (halfSpaceModelHomeomorph dimension point).val 0 = 0 ↔ point.val.1 = 0 := by
  rw [halfSpaceModelHomeomorph_apply_zero]

/-- A finite-dimensional real ambient space admits the same product chart model.
The positive dimension instance is supplied locally by each application. -/
noncomputable def finiteDimensionalProductCoordinates (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] :
    E ≃L[ℝ] (ℝ × (Fin (Module.finrank ℝ E - 1) → ℝ)) :=
  (ContinuousLinearEquiv.ofFinrankEq (show Module.finrank ℝ E =
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) by
      rw [finrank_euclideanSpace_fin])).trans
    (productEuclideanCoordinates (Module.finrank ℝ E)).symm

end BoundedUncertainty
