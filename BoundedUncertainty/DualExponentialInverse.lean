import BoundedUncertainty.DualBoundaryInterfaces
import BoundedUncertainty.SelfSurjectivity

/-! The inverse formulation following Theorem 4.16. The exponential map is
inverted on the actual unit-normal bundle, where bijectivity has been proved.
An ambient representative is used only to express the manuscript's set image. -/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

noncomputable def SetValuedSystem.wholeSpaceExponentialMap
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hcontraction : system.IsContraction) :
    E × {n : E // ‖n‖ = 1} → E × {n : E // ‖n‖ = 1} :=
  fun p => system.exponentialLift hcontraction (⟨p.1, hwhole ▸ mem_univ p.1⟩, p.2)

theorem SetValuedSystem.bijective_wholeSpaceExponentialMap
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) :
    Function.Bijective (system.wholeSpaceExponentialMap hwhole hcontraction) := by
  constructor
  · intro p q hequal
    have hpq := system.exponentialMap_inj_of_ball_subset hcontraction p.1 q.1 p.2 q.2
      (hwhole ▸ mem_univ _) (hwhole ▸ mem_univ _)
      (by rw [hwhole]; exact subset_univ _) (by rw [hwhole]; exact subset_univ _)
      p.2.property q.2.property (congrArg (fun t => (t.1, (t.2 : E))) hequal)
    exact Prod.ext (congrArg (fun t : E × E => t.1) hpq)
      (Subtype.ext (congrArg (fun t : E × E => t.2) hpq))
  · intro p
    obtain ⟨q, hq⟩ := system.exponentialLift_covers_domain_of_image_eq_domain
      hcontraction hself (⟨p.1, hwhole ▸ mem_univ _⟩, p.2)
    exact ⟨((q.1 : E), q.2), hq⟩

/-- The genuine inverse is the inverse of a proved bijection on unit normals. -/
noncomputable def SetValuedSystem.wholeSpaceExponentialEquiv
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) :
    (E × {n : E // ‖n‖ = 1}) ≃ (E × {n : E // ‖n‖ = 1}) :=
  Equiv.ofBijective _ (system.bijective_wholeSpaceExponentialMap hwhole hself hcontraction)

/-- Off the unit bundle the ambient representative is assigned the identity.
No inverse claim is made there. -/
noncomputable def SetValuedSystem.exponentialInverseOnAmbient
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (p : E × E) : E × E := by
  classical
  exact if hunit : ‖p.2‖ = 1 then
    let q := (system.wholeSpaceExponentialEquiv hwhole hself hcontraction).symm
      (p.1, ⟨p.2, hunit⟩)
    (q.1, (q.2 : E))
  else p

theorem SetValuedSystem.exponentialInverseOnAmbient_exponentialMap
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (p : E × E) (hunit : ‖p.2‖ = 1) :
    system.exponentialInverseOnAmbient hwhole hself hcontraction
      (exponentialMap system.radius system.radiusGradientOnAmbient p) = p := by
  have houtput := exponentialMap_normal_unit system.radius system.radiusGradientOnAmbient
    p.1 p.2 (hcontraction.norm_radiusGradientOnAmbient _ (hwhole ▸ mem_univ _)) hunit
  rw [SetValuedSystem.exponentialInverseOnAmbient, dif_pos houtput]
  have hequal := (system.wholeSpaceExponentialEquiv hwhole hself hcontraction).symm_apply_apply
    (p.1, ⟨p.2, hunit⟩)
  exact congrArg (fun q => (q.1, (q.2 : E))) hequal

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The displayed inverse formula after 4.16, retaining the two-sided nearest
point assumptions (attainment suffices) and the actual graph-based normals. -/
theorem SetValuedSystem.image_exponentialInverseOnAmbient_inwardNormalBundle
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hregular : IsRegularClosed A)
    (hdualregular : IsRegularClosed (dualInflation system.radius A))
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (target : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    system.exponentialInverseOnAmbient hwhole hself hcontraction ''
      inwardNormalBundle A hregular source =
        inwardNormalBundle (dualInflation system.radius A) hdualregular target := by
  rw [← system.image_exponentialMap_inwardNormalBundle_dualInflation hwhole hcontraction
    hpositive A hregular hdualregular source target hnearest hvisible, image_image]
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    simpa only [Function.comp_apply,
      system.exponentialInverseOnAmbient_exponentialMap hwhole hself hcontraction q
        (inwardNormalBundle_subset _ hdualregular target hq).2] using hq
  · intro p hp
    exact ⟨p, hp, system.exponentialInverseOnAmbient_exponentialMap hwhole hself hcontraction p
      (inwardNormalBundle_subset _ hdualregular target hp).2⟩

/-- Original hypothesis interface: dual regular closedness is derived from
nearest-point attainment, rather than imposed as an additional assumption. -/
theorem SetValuedSystem.image_exponentialInverseOnAmbient_of_two_sided_nearest
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (A : Set E) (hregular : IsRegularClosed A)
    (source : (x : frontier A) → C1FrontierGraphAt (F := F) A x)
    (target : (y : frontier (dualInflation system.radius A)) →
      C1FrontierGraphAt (F := G) (dualInflation system.radius A) y)
    (hnearest : ∀ y ∈ frontier (dualInflation system.radius A),
      ∃ x ∈ A, dist y x = Metric.infDist y A)
    (hvisible : ∀ x ∈ frontier A, ∃ y ∈ frontier (dualInflation system.radius A),
      dist y x = Metric.infDist y A) :
    system.exponentialInverseOnAmbient hwhole hself hcontraction ''
      inwardNormalBundle A hregular source =
        inwardNormalBundle (dualInflation system.radius A)
          (system.isRegularClosed_dualInflation_of_boundary_nearest hwhole hcontraction
            hpositive A hnearest) target :=
  system.image_exponentialInverseOnAmbient_inwardNormalBundle hwhole hself hcontraction
    hpositive A hregular _ source target hnearest hvisible

end BoundedUncertainty
