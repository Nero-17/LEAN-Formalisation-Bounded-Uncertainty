import BoundedUncertainty.NormalBundleNotation
import BoundedUncertainty.HigherBoundaryMap

/-!
# The boundary-map image of a fixed source fibre

Proposition 4.11 is proved using contraction only at the image of the fixed
source point. The positive-radius ball's outward normal bundle is constructed
from its actual squared-distance defining function, rather than defined by a
radial parameterization. The radial parameterization is then proved equal to
that bundle. At zero radius only the parameterized image formula is asserted.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual outward normal bundle from the ball's regular defining function. -/
noncomputable def closedBallOutwardNormalBundle (y : E) (R : ℝ) (hR : 0 < R) : Set (E × E) :=
  range (fun z : frontier (Metric.closedBall y R) =>
    ((z : E), (C1BoundaryAt.closedBall y R z hR
      (Metric.frontier_closedBall_subset_sphere z.property)).normal))

/-- Projecting this actual normal bundle recovers exactly the ball frontier. -/
theorem image_fst_closedBallOutwardNormalBundle (y : E) (R : ℝ) (hR : 0 < R) :
    Prod.fst '' closedBallOutwardNormalBundle y R hR = frontier (Metric.closedBall y R) := by
  ext z
  constructor
  · rintro ⟨p, ⟨w, rfl⟩, rfl⟩
    exact w.property
  · intro hz
    exact ⟨_, ⟨⟨z, hz⟩, rfl⟩, rfl⟩

/-- Its radial parameterization follows from the actual gradient of squared distance. -/
theorem closedBallOutwardNormalBundle_eq_radial [Nontrivial E]
    (y : E) (R : ℝ) (hR : 0 < R) :
    closedBallOutwardNormalBundle y R hR =
      range (fun u : {n : E // ‖n‖ = 1} => (y + R • (u : E), (u : E))) := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨(C1BoundaryAt.closedBall y R z hR
      (Metric.frontier_closedBall_subset_sphere z.property)).normal,
      (C1BoundaryAt.closedBall y R z hR
        (Metric.frontier_closedBall_subset_sphere z.property)).normal_unit⟩, ?_⟩
    apply Prod.ext
    · change y + R • (C1BoundaryAt.closedBall y R z hR
        (Metric.frontier_closedBall_subset_sphere z.property)).normal = (z : E)
      rw [C1BoundaryAt.closedBall_normal_eq_inv_radius_smul, smul_smul,
        mul_inv_cancel₀ hR.ne', one_smul]
      abel
    · rfl
  · rintro ⟨u, rfl⟩
    have hz : y + R • (u : E) ∈ frontier (Metric.closedBall y R) := by
      rw [frontier_closedBall']
      change dist (y + R • (u : E)) y = R
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hR, u.property, mul_one]
    refine ⟨⟨y + R • (u : E), hz⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change (C1BoundaryAt.closedBall y R (y + R • (u : E)) hR
        (Metric.frontier_closedBall_subset_sphere hz)).normal = (u : E)
      rw [C1BoundaryAt.closedBall_normal_eq_inv_radius_smul, add_sub_cancel_left,
        smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Agreement with Notation 3.3 for every choice of valid ball-frontier charts. -/
theorem closedBallOutwardNormalBundle_eq_outwardNormalBundle
    (y : E) (R : ℝ) (hR : 0 < R) (hregular : IsRegularClosed (Metric.closedBall y R))
    (charts : (z : frontier (Metric.closedBall y R)) →
      C1FrontierGraphAt (F := F) (Metric.closedBall y R) z) :
    closedBallOutwardNormalBundle y R hR =
      outwardNormalBundle (Metric.closedBall y R) hregular charts := by
  apply congrArg range
  funext z
  apply Prod.ext
  · rfl
  · exact (C1BoundaryAt.closedBall y R z hR
      (Metric.frontier_closedBall_subset_sphere z.property)).normal_eq_of_subset
      ((charts z).toC1BoundaryAt hregular) Set.Subset.rfl

variable {r s : ℕ}

/-- The fixed-fibre image formula needs contraction at just the fixed image point. -/
theorem SetValuedSystem.image_boundaryFormula_fibre_eq_radial
    (system : SetValuedSystem (E := E) r s) (x : system.domain)
    (hgradient : ‖system.radiusGradientOnAmbient (system.map x)‖ < 1) :
    system.boundaryFormula '' ({x} ×ˢ (univ : Set {n : E // ‖n‖ = 1})) =
      range (fun u : {n : E // ‖n‖ = 1} =>
        (system.map x + system.radius (system.map x) • (u : E), (u : E))) := by
  ext p
  constructor
  · rintro ⟨⟨source, n⟩, ⟨hsource, _⟩, rfl⟩
    have hsourceEq : source = x := hsource
    subst source
    refine ⟨normalSphereHomeomorph (system.radiusGradientOnAmbient (system.map x)) hgradient
      (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv x)) n), rfl⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨n, hn⟩ := ((normalizedLinearHomeomorph
      (inverseTranspose (system.derivativeEquiv x))).trans
        (normalSphereHomeomorph (system.radiusGradientOnAmbient (system.map x)) hgradient)).surjective u
    refine ⟨(x, n), ⟨rfl, mem_univ n⟩, ?_⟩
    have hnormal := congrArg (fun v : {n : E // ‖n‖ = 1} => (v : E)) hn
    change normalUpdate (system.radiusGradientOnAmbient (system.map x))
      (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv x)) n : E) = (u : E)
      at hnormal
    change exponentialMap system.radius system.radiusGradientOnAmbient
      (system.map x, (normalizedLinearHomeomorph (inverseTranspose (system.derivativeEquiv x)) n : E)) = _
    simp only [exponentialMap, hnormal]

/-- Proposition 4.11 with the actual ball boundary and its actual outward normals. -/
theorem SetValuedSystem.image_boundaryFormula_fibre_eq_closedBallOutwardNormalBundle
    (system : SetValuedSystem (E := E) r s) (x : system.domain)
    (hpositive : 0 < system.radius (system.map x))
    (hgradient : ‖system.radiusGradientOnAmbient (system.map x)‖ < 1) :
    system.boundaryFormula '' ({x} ×ˢ (univ : Set {n : E // ‖n‖ = 1})) =
      closedBallOutwardNormalBundle (system.map x) (system.radius (system.map x)) hpositive := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (lt_of_lt_of_le (by decide : 0 < 2) system.dimension_at_least_two)
  rw [closedBallOutwardNormalBundle_eq_radial]
  exact system.image_boundaryFormula_fibre_eq_radial x hgradient

/-- The identical assertion for the ambient coordinates of the genuine typed beta map. -/
theorem SetValuedSystem.image_boundaryMap_fibre_eq_closedBallOutwardNormalBundle
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (x : system.domain) (hpositive : 0 < system.radius (system.map x)) :
    (fun p => (((system.boundaryMap hcontraction p).1 : E),
      ((system.boundaryMap hcontraction p).2 : E))) ''
        ({x} ×ˢ (univ : Set {n : E // ‖n‖ = 1})) =
      closedBallOutwardNormalBundle (system.map x) (system.radius (system.map x)) hpositive :=
  system.image_boundaryFormula_fibre_eq_closedBallOutwardNormalBundle x hpositive
    (hcontraction.norm_radiusGradientOnAmbient _ (system.map_into_domain x.property))

/-- Proposition 4.11 expressed using any charts in the existing normal-bundle notation. -/
theorem SetValuedSystem.image_boundaryFormula_fibre_eq_outwardNormalBundle
    (system : SetValuedSystem (E := E) r s) (x : system.domain)
    (hpositive : 0 < system.radius (system.map x))
    (hgradient : ‖system.radiusGradientOnAmbient (system.map x)‖ < 1)
    (hregular : IsRegularClosed (Metric.closedBall (system.map x) (system.radius (system.map x))))
    (charts : (z : frontier (Metric.closedBall (system.map x) (system.radius (system.map x)))) →
      C1FrontierGraphAt (F := F) (Metric.closedBall (system.map x) (system.radius (system.map x))) z) :
    system.boundaryFormula '' ({x} ×ˢ (univ : Set {n : E // ‖n‖ = 1})) =
      outwardNormalBundle (Metric.closedBall (system.map x) (system.radius (system.map x)))
        hregular charts :=
  (system.image_boundaryFormula_fibre_eq_closedBallOutwardNormalBundle x hpositive hgradient).trans
    (closedBallOutwardNormalBundle_eq_outwardNormalBundle _ _ hpositive hregular charts)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The exact first set-valued iterate of a singleton, used in Example 4.12. -/
theorem setValuedImage_singleton (f : E → E) (radius : E → ℝ) (x : E) :
    setValuedImage f radius {x} = Metric.closedBall (f x) (radius (f x)) := by
  simp only [setValuedImage, mem_singleton_iff, iUnion_iUnion_eq_left]

/-- The mathematical initialization in Example 4.12: one boundary-map step
and projection give the frontier of the first set-valued singleton iterate. -/
theorem SetValuedSystem.image_fst_boundaryFormula_fibre_eq_frontier_singleton_image
    (system : SetValuedSystem (E := E) r s) (x : system.domain)
    (hpositive : 0 < system.radius (system.map x))
    (hgradient : ‖system.radiusGradientOnAmbient (system.map x)‖ < 1) :
    Prod.fst '' (system.boundaryFormula '' ({x} ×ˢ (univ : Set {n : E // ‖n‖ = 1}))) =
      frontier (setValuedImage system.map system.radius {(x : E)}) := by
  rw [system.image_boundaryFormula_fibre_eq_closedBallOutwardNormalBundle x hpositive hgradient,
    image_fst_closedBallOutwardNormalBundle, setValuedImage_singleton]

end BoundedUncertainty
