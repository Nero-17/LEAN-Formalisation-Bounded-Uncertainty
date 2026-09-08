import BoundedUncertainty.BoundaryProjectionTopology

/-!
The actual recipient parametrization in Theorem 4.9, before recipient C1
regularity is proved. Its centre and normal fields come from Gamma inverse
and the genuine system boundary map.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}


variable (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
  (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
  (source : (x : frontier A) → C1BoundaryAt A x)
  (hinjective : Function.Injective (system.boundaryProjection A hA source))
  (hrange : range (system.boundaryProjection A hA source) =
    frontier (setValuedImage system.map system.radius A))

noncomputable def SetValuedSystem.recipientSource
    (z : frontier (setValuedImage system.map system.radius A)) : frontier A :=
  (system.boundaryProjectionHomeomorph hcontraction A hA hcompact source hinjective hrange).symm z

noncomputable def SetValuedSystem.recipientCenter
    (z : frontier (setValuedImage system.map system.radius A)) : E :=
  system.map (system.recipientSource hcontraction A hA hcompact source hinjective hrange z)

noncomputable def SetValuedSystem.recipientNormal
    (z : frontier (setValuedImage system.map system.radius A)) : E :=
  ((system.boundaryMap hcontraction (system.boundaryNormalInput A hA source
    (system.recipientSource hcontraction A hA hcompact source hinjective hrange z))).2 : E)

theorem SetValuedSystem.continuous_recipientSource :
    Continuous (system.recipientSource hcontraction A hA hcompact source hinjective hrange) :=
  (system.boundaryProjectionHomeomorph hcontraction A hA hcompact source hinjective hrange).symm.continuous

theorem SetValuedSystem.recipientCenter_mem_image
    (z : frontier (setValuedImage system.map system.radius A)) :
    system.recipientCenter hcontraction A hA hcompact source hinjective hrange z ∈ system.map '' A :=
  ⟨system.recipientSource hcontraction A hA hcompact source hinjective hrange z,
    (source _).mem, rfl⟩

theorem SetValuedSystem.recipientCenter_mem_frontier_image
    (z : frontier (setValuedImage system.map system.radius A)) :
    system.recipientCenter hcontraction A hA hcompact source hinjective hrange z ∈
      frontier (system.map '' A) := by
  rw [system.diffeomorphism.frontier_image system.map_order_pos hA hcompact]
  exact ⟨system.recipientSource hcontraction A hA hcompact source hinjective hrange z,
    (system.recipientSource hcontraction A hA hcompact source hinjective hrange z).property, rfl⟩

theorem SetValuedSystem.norm_recipientNormal
    (z : frontier (setValuedImage system.map system.radius A)) :
    ‖system.recipientNormal hcontraction A hA hcompact source hinjective hrange z‖ = 1 :=
  (system.boundaryMap hcontraction (system.boundaryNormalInput A hA source
    (system.recipientSource hcontraction A hA hcompact source hinjective hrange z))).2.property

theorem SetValuedSystem.continuous_recipientCenter :
    Continuous (system.recipientCenter hcontraction A hA hcompact source hinjective hrange) := by
  have hinput : Continuous (system.boundaryNormalInput A hA source) :=
    (continuous_subtype_val.subtype_mk _).prodMk
      ((continuous_boundaryNormal source).subtype_mk _)
  have hmap : Continuous (fun x : system.domain => system.map x) :=
    continuousOn_iff_continuous_restrict.mp system.diffeomorphism.forward_extension.continuousOn
  exact hmap.comp (continuous_fst.comp (hinput.comp
    (system.continuous_recipientSource hcontraction A hA hcompact source hinjective hrange)))

theorem SetValuedSystem.continuous_recipientNormal :
    Continuous (system.recipientNormal hcontraction A hA hcompact source hinjective hrange) := by
  have hinput : Continuous (system.boundaryNormalInput A hA source) :=
    (continuous_subtype_val.subtype_mk _).prodMk
      ((continuous_boundaryNormal source).subtype_mk _)
  exact continuous_subtype_val.comp (continuous_snd.comp
    ((system.continuous_boundaryMap hcontraction).comp (hinput.comp
      (system.continuous_recipientSource hcontraction A hA hcompact source hinjective hrange))))

/-- The source selected by Gamma inverse supplies the exact radial position. -/
theorem SetValuedSystem.recipient_radial_position
    (z : frontier (setValuedImage system.map system.radius A)) :
    (z : E) = system.recipientCenter hcontraction A hA hcompact source hinjective hrange z +
      system.radius (system.recipientCenter hcontraction A hA hcompact source hinjective hrange z) •
        system.recipientNormal hcontraction A hA hcompact source hinjective hrange z := by
  have hprojection : system.boundaryProjection A hA source
      (system.recipientSource hcontraction A hA hcompact source hinjective hrange z) = (z : E) :=
    congrArg Subtype.val
      ((system.boundaryProjectionHomeomorph hcontraction A hA hcompact source hinjective hrange).apply_symm_apply z)
  exact hprojection.symm

theorem SetValuedSystem.recipientCenter_injective :
    Function.Injective (system.recipientCenter hcontraction A hA hcompact source hinjective hrange) := by
  intro z w heq
  apply (system.boundaryProjectionHomeomorph hcontraction A hA hcompact source hinjective hrange).symm.injective
  apply Subtype.ext
  exact system.diffeomorphism.injectiveOn (hA (source _).mem) (hA (source _).mem) heq

/-- At a zero-radius centre, the actual output normal is the source-image outward normal.
The radius gradient may be a nonzero inward multiple of that normal. -/
theorem SetValuedSystem.recipientNormal_eq_imageBoundary_normal_at_zero
    (z : frontier (setValuedImage system.map system.radius A))
    (boundary : C1BoundaryAt (system.map '' A)
      (system.recipientCenter hcontraction A hA hcompact source hinjective hrange z))
    (hzero : system.radius
      (system.recipientCenter hcontraction A hA hcompact source hinjective hrange z) = 0) :
    system.recipientNormal hcontraction A hA hcompact source hinjective hrange z = boundary.normal := by
  have hnormal := system.imageBoundary_normal A hA hcompact
    (system.recipientSource hcontraction A hA hcompact source hinjective hrange z)
    (source _) boundary
  change normalUpdate (system.radiusGradientOnAmbient
    (system.recipientCenter hcontraction A hA hcompact source hinjective hrange z))
    (normalizedLinearMap (inverseTranspose (system.derivativeEquiv
      ⟨system.recipientSource hcontraction A hA hcompact source hinjective hrange z,
        hA (source _).mem⟩)) (source _).normal) = boundary.normal
  rw [← hnormal]
  have himage : system.map '' A ⊆ system.domain := by
    rintro y ⟨x, hx, rfl⟩
    exact system.map_into_domain (hA hx)
  obtain ⟨coefficient, _, hgradient⟩ :=
    system.exists_nonpos_radiusGradient_smul_at_zero (system.map '' A) himage _ boundary hzero
  rw [hgradient, normalUpdate_smul_self _ _ boundary.normal_unit]

end BoundedUncertainty
