import BoundedUncertainty.DualBoundaryContact
import BoundedUncertainty.WholeSpaceNormalTransport
import BoundedUncertainty.DiffeomorphismBoundaryNormal
import BoundedUncertainty.InvariantBoundaryExtensions

/-!
Corollary 4.18 for the actual dual-invariant set and its actual inward normal
bundle. The dual-inflation boundary data are constructed from the deterministic
image; no extra charts for that image or for a preimage are assumed.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

omit [CompleteSpace E] in
theorem SetValuedSystem.dualInflation_eq_image_of_dualInvariant
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) (M : Set E)
    (hinvariant : dualSetMap system.map system.radius M = M) :
    dualInflation system.radius M = system.map '' M := by
  rw [dualSetMap_eq_preimage] at hinvariant
  calc
    dualInflation system.radius M = system.map '' (system.map ⁻¹' dualInflation system.radius M) :=
      (image_preimage_eq _ (show Function.Surjective system.map from
        (system.wholeSpaceHomeomorph hwhole hself).surjective)).symm
    _ = system.map '' M := congrArg (fun B => system.map '' B) hinvariant

/-- The true beta formula at an attained contact of a dual-invariant set. -/
theorem SetValuedSystem.boundaryFormulaOnAmbient_inward_of_dualInvariant_contact
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (M : Set E) (hcompact : IsCompact M)
    (hinvariant : dualSetMap system.map system.radius M = M) (a x : E)
    (source : C1BoundaryAt M a) (recipient : C1BoundaryAt M x)
    (hpositive : 0 < system.radius (system.map a))
    (hcontact : dist x (system.map a) = system.radius (system.map a))
    (hnearest : ∀ w ∈ M, system.radius (system.map a) ≤ dist w (system.map a)) :
    system.boundaryFormulaOnAmbient (a, -source.normal) = (x, -recipient.normal) := by
  have hM : M ⊆ system.domain := fun w _ => hwhole ▸ mem_univ w
  have himage := system.dualInflation_eq_image_of_dualInvariant hwhole hself M hinvariant
  obtain ⟨imageBoundary, hnormal⟩ := system.exists_imageBoundary M hM hcompact a source
  let target : C1BoundaryAt (dualInflation system.radius M) (system.map a) :=
    { imageBoundary with
      mem_iff := by
        intro w hw
        rw [himage]
        exact imageBoundary.mem_iff w hw }
  have hpair : system.linearLiftOnAmbient (a, -source.normal) =
      (system.map a, -target.normal) := by
    rw [system.linearLiftOnAmbient_apply
      (⟨a, hM source.mem⟩, ⟨-source.normal, (norm_neg _).trans source.normal_unit⟩)]
    apply Prod.ext
    · rfl
    · change normalizedLinearMap (inverseTranspose (system.derivativeEquiv ⟨a, hM source.mem⟩))
        (-source.normal) = -imageBoundary.normal
      rw [hnormal]
      simp only [normalizedLinearMap, map_neg, norm_neg, smul_neg]
  change exponentialMap system.radius system.radiusGradientOnAmbient
    (system.linearLiftOnAmbient (a, -source.normal)) = _
  rw [hpair]
  exact system.exponentialMap_inward_of_dual_contact hwhole hcontraction M x (system.map a)
    recipient target hpositive hcontact hnearest

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual forward invariance of the inward bundle, with only source charts given. -/
theorem SetValuedSystem.image_inwardNormalBundle_of_dualInvariant
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (M : Set E) (hcompact : IsCompact M) (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hinvariant : dualSetMap system.map system.radius M = M)
    (hvisible : ∀ x ∈ frontier M, ∃ y ∈ frontier (dualInflation system.radius M),
      dist y x = Metric.infDist y M) :
    system.boundaryFormulaOnAmbient '' inwardNormalBundle M hregular boundary =
      inwardNormalBundle M hregular boundary := by
  have hM : M ⊆ system.domain := fun w _ => hwhole ▸ mem_univ w
  have himage := system.dualInflation_eq_image_of_dualInvariant hwhole hself M hinvariant
  have hfrontier : frontier (dualInflation system.radius M) = system.map '' frontier M := by
    rw [himage, system.diffeomorphism.frontier_image system.map_order_pos hM hcompact]
  apply Subset.antisymm
  · rintro p ⟨q, ⟨a, rfl⟩, rfl⟩
    have ha : (a : E) ∈ M := hregular.isClosed.frontier_subset a.property
    have htarget : system.map a ∈ frontier (dualInflation system.radius M) :=
      hfrontier.symm ▸ mem_image_of_mem system.map a.property
    have hlevel := system.infDist_eq_radius_of_mem_frontier_dualInflation hwhole M
      ⟨a, ha⟩ (system.map a) htarget
    obtain ⟨x, hx, hxy⟩ := hcompact.exists_infDist_eq_dist ⟨a, ha⟩ (system.map a)
    have hcontact : dist x (system.map a) = system.radius (system.map a) :=
      (dist_comm _ _).trans (hxy.symm.trans hlevel)
    have hnearest : ∀ w ∈ M, system.radius (system.map a) ≤ dist w (system.map a) :=
      fun w hw => hlevel.symm.trans_le
        ((Metric.infDist_le_dist_of_mem hw).trans_eq (dist_comm _ _))
    have hxfrontier := mem_frontier_of_nearest_contact M x (system.map a)
      (system.radius (system.map a)) hx (hpositive _) hcontact hnearest
    exact ⟨⟨x, hxfrontier⟩,
      (system.boundaryFormulaOnAmbient_inward_of_dualInvariant_contact hwhole hself hcontraction
        M hcompact hinvariant a x ((boundary a).toC1BoundaryAt hregular)
        ((boundary ⟨x, hxfrontier⟩).toC1BoundaryAt hregular) (hpositive _) hcontact hnearest).symm⟩
  · rintro p ⟨x, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hvisible x x.property
    obtain ⟨a, ha, hay⟩ := hfrontier ▸ hy
    have hx : (x : E) ∈ M := hregular.isClosed.frontier_subset x.property
    have hlevel := system.infDist_eq_radius_of_mem_frontier_dualInflation hwhole M ⟨x, hx⟩ y hy
    have hcontact : dist (x : E) (system.map a) = system.radius (system.map a) := by
      rw [hay, dist_comm]
      exact hxy.trans hlevel
    have hnearest : ∀ w ∈ M, system.radius (system.map a) ≤ dist w (system.map a) := by
      intro w hw
      rw [hay]
      exact hlevel.symm.trans_le ((Metric.infDist_le_dist_of_mem hw).trans_eq (dist_comm _ _))
    refine ⟨inwardNormalPair M hregular boundary ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    exact system.boundaryFormulaOnAmbient_inward_of_dualInvariant_contact hwhole hself hcontraction
      M hcompact hinvariant a x ((boundary ⟨a, ha⟩).toC1BoundaryAt hregular)
      ((boundary x).toC1BoundaryAt hregular) (hpositive _) hcontact hnearest

/-- Corollary 4.18's actual inverse-boundary invariance. -/
theorem SetValuedSystem.image_boundaryInverseOnAmbient_inwardNormalBundle_of_dualInvariant
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (M : Set E) (hcompact : IsCompact M) (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hinvariant : dualSetMap system.map system.radius M = M)
    (hvisible : ∀ x ∈ frontier M, ∃ y ∈ frontier (dualInflation system.radius M),
      dist y x = Metric.infDist y M) :
    system.boundaryInverseOnAmbient hcontraction '' inwardNormalBundle M hregular boundary =
      inwardNormalBundle M hregular boundary := by
  have hbundle : inwardNormalBundle M hregular boundary ⊆
      system.domain ×ˢ {n : E | ‖n‖ = 1} := by
    intro p hp
    exact ⟨hwhole ▸ mem_univ p.1, (inwardNormalBundle_subset M hregular boundary hp).2⟩
  have himage := system.image_inwardNormalBundle_of_dualInvariant hwhole hself hcontraction hpositive
    M hcompact hregular boundary hinvariant hvisible
  calc
    system.boundaryInverseOnAmbient hcontraction '' inwardNormalBundle M hregular boundary =
        system.boundaryInverseOnAmbient hcontraction ''
          (system.boundaryFormulaOnAmbient '' inwardNormalBundle M hregular boundary) :=
      congrArg (fun B => system.boundaryInverseOnAmbient hcontraction '' B) himage.symm
    _ = inwardNormalBundle M hregular boundary :=
      (system.boundaryInverseOnAmbient_leftInvOn hcontraction).image_image' hbundle

/-- The restriction is an actual homeomorphism and has both asserted local regularities. -/
theorem SetValuedSystem.dualInvariant_inwardNormalBundle_regular_homeomorphism
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (M : Set E) (hcompact : IsCompact M) (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hinvariant : dualSetMap system.map system.radius M = M)
    (hvisible : ∀ x ∈ frontier M, ∃ y ∈ frontier (dualInflation system.radius M),
      dist y x = Metric.infDist y M) :
    (∃ equivalence : inwardNormalBundle M hregular boundary ≃ₜ inwardNormalBundle M hregular boundary,
      (∀ p, (equivalence p : E × E) = system.boundaryFormulaOnAmbient p) ∧
      (∀ p, (equivalence.symm p : E × E) = system.boundaryInverseOnAmbient hcontraction p)) ∧
    HasLocalExtensionOn (min r s - 1) (inwardNormalBundle M hregular boundary)
      system.boundaryFormulaOnAmbient ∧
    HasLocalExtensionOn (min r s - 1) (inwardNormalBundle M hregular boundary)
      (system.boundaryInverseOnAmbient hcontraction) := by
  have hbundle : inwardNormalBundle M hregular boundary ⊆
      system.domain ×ˢ {n : E | ‖n‖ = 1} := by
    intro p hp
    exact ⟨hwhole ▸ mem_univ p.1, (inwardNormalBundle_subset M hregular boundary hp).2⟩
  have himage := system.image_inwardNormalBundle_of_dualInvariant hwhole hself hcontraction
    hpositive M hcompact hregular boundary hinvariant hvisible
  exact ⟨⟨system.boundaryHomeomorphInvariant hcontraction _ hbundle himage,
      fun _ => rfl, fun _ => rfl⟩,
    (system.hasLocalExtensionOn_boundaryFormulaOnAmbient hcontraction).mono_domain hbundle,
    (system.hasLocalExtensionOn_boundaryInverseOnAmbient hcontraction).mono_domain
      (system.invariant_subset_range_boundaryFormula _ hbundle himage)⟩

/-- The finite local extensions take sphere values and retain the full-bundle nonsingular differential. -/
theorem SetValuedSystem.dualInvariant_inwardNormalBundle_regular_sphere_extensions
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (M : Set E) (hcompact : IsCompact M) (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hinvariant : dualSetMap system.map system.radius M = M)
    (hvisible : ∀ x ∈ frontier M, ∃ y ∈ frontier (dualInflation system.radius M),
      dist y x = Metric.infDist y M)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (p : E × E) (hp : p ∈ inwardNormalBundle M hregular boundary) :
    ∃ extension : LocalExtensionAt (min r s - 1) (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ inverseExtension : LocalExtensionAt (min r s - 1) (range system.boundaryFormula)
          (system.boundaryInverseOnAmbient hcontraction) p,
        (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
        (∀ q ∈ inverseExtension.neighborhood, ‖(inverseExtension.extension q).2‖ = 1) ∧
        ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
            bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
          ∀ v : bundleTangentSpace p.2,
            (differential v : E × E) = fderiv ℝ extension.extension p v := by
  apply system.exists_regular_sphere_boundaryExtensions_on_invariant hcontraction
    (inwardNormalBundle M hregular boundary) _
    (system.image_inwardNormalBundle_of_dualInvariant hwhole hself hcontraction hpositive
      M hcompact hregular boundary hinvariant hvisible) hr hs p hp
  intro q hq
  exact ⟨hwhole ▸ mem_univ q.1, (inwardNormalBundle_subset M hregular boundary hq).2⟩

/-- The smooth counterpart uses one fixed smooth sphere-valued neighborhood for each witness. -/
theorem SetValuedSystem.dualInvariant_inwardNormalBundle_smooth_sphere_extensions
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain)
    (hcontraction : system.IsContraction) (hpositive : ∀ y : E, 0 < system.radius y)
    (hmap : HasSmoothLocalExtensionOn system.domain system.map)
    (hradius : HasSmoothLocalExtensionOn system.domain system.radius)
    (hinverse : HasSmoothLocalExtensionOn (system.map '' system.domain) system.diffeomorphism.inverse)
    (M : Set E) (hcompact : IsCompact M) (hregular : IsRegularClosed M)
    (boundary : (x : frontier M) → C1FrontierGraphAt (F := F) M x)
    (hinvariant : dualSetMap system.map system.radius M = M)
    (hvisible : ∀ x ∈ frontier M, ∃ y ∈ frontier (dualInflation system.radius M),
      dist y x = Metric.infDist y M)
    (p : E × E) (hp : p ∈ inwardNormalBundle M hregular boundary) :
    ∃ extension : SmoothLocalExtensionAt (system.domain ×ˢ {n : E | ‖n‖ = 1})
        system.boundaryFormulaOnAmbient p,
      ∃ inverseExtension : SmoothLocalExtensionAt (range system.boundaryFormula)
          (system.boundaryInverseOnAmbient hcontraction) p,
        (∀ q ∈ extension.neighborhood, ‖(extension.extension q).2‖ = 1) ∧
        (∀ q ∈ inverseExtension.neighborhood, ‖(inverseExtension.extension q).2‖ = 1) ∧
        ∃ differential : bundleTangentSpace p.2 ≃L[ℝ]
            bundleTangentSpace (system.boundaryFormulaOnAmbient p).2,
          ∀ v : bundleTangentSpace p.2,
            (differential v : E × E) = fderiv ℝ extension.extension p v := by
  apply system.exists_smooth_sphere_boundaryExtensions_on_invariant hcontraction hmap hradius hinverse
    (inwardNormalBundle M hregular boundary) _
    (system.image_inwardNormalBundle_of_dualInvariant hwhole hself hcontraction hpositive
      M hcompact hregular boundary hinvariant hvisible) p hp
  intro q hq
  exact ⟨hwhole ▸ mem_univ q.1, (inwardNormalBundle_subset M hregular boundary hq).2⟩

end BoundedUncertainty
