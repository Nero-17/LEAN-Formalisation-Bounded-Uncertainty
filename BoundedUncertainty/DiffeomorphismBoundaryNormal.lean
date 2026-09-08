import BoundedUncertainty.DiffeomorphismSetGeometry
import BoundedUncertainty.C1FrontierContact

/-!
Outward normals under the actual ambient diffeomorphism in Section 4.
The image boundary is constructed from the source defining function and a
local inverse of a nonsingular extension. Compactness excludes other
preimages. Neither a closed image of the whole domain nor an image boundary
chart is assumed.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {order : ℕ} {X A : Set E} {f : E → E} {x : E}

/-- A local nonsingular extension transports the boundary and its outward normal.
The assumptions on the given map are relative to its actual domain. -/
theorem NonsingularLocalExtensionAt.exists_imageBoundary
    (extension : NonsingularLocalExtensionAt order X f x) (horder : 1 ≤ order)
    (hA : A ⊆ X) (hcompact : IsCompact A) (hcontinuous : ContinuousOn f A)
    (hinjective : Set.InjOn f X) (source : C1BoundaryAt A x) :
    ∃ target : C1BoundaryAt (f '' A) (f x),
      target.normal = normalizedLinearMap (inverseTranspose extension.derivative) source.normal := by
  have hsmooth : ContDiffAt ℝ 1 extension.extension x :=
    (extension.contDiffOn_extension.of_le (by exact_mod_cast horder)).contDiffAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  let coordinates := (hsmooth.toOpenPartialHomeomorph extension.extension
    extension.hasFDerivAt_extension one_ne_zero).restrOpen
      (extension.neighborhood ∩ source.neighborhood)
      (extension.isOpen_neighborhood.inter source.isOpen_neighborhood)
  have hxsource : x ∈ coordinates.source :=
    ⟨hsmooth.mem_toOpenPartialHomeomorph_source extension.hasFDerivAt_extension one_ne_zero,
      extension.mem_neighborhood, source.mem_neighborhood⟩
  have hagrees : Set.EqOn coordinates f (X ∩ coordinates.source) := by
    intro z hz
    exact extension.agrees ⟨hz.1, hz.2.2.1⟩
  have hforward : coordinates x = f x := hagrees ⟨hA source.mem, hxsource⟩
  have htarget : f x ∈ coordinates.target := hforward ▸ coordinates.map_source hxsource
  have hinverse : coordinates.symm (f x) = x := by
    rw [← hforward]
    exact coordinates.left_inv hxsource
  have hderivative : HasFDerivAt coordinates
      (extension.derivative : E →L[ℝ] E) (coordinates.symm (f x)) := by
    rw [hinverse]
    exact extension.hasFDerivAt_extension
  have hsmoothInverse : ContDiffAt ℝ 1 coordinates.symm (f x) := by
    apply coordinates.contDiffAt_symm (f₀' := extension.derivative) htarget hderivative
    rw [hinverse]
    exact hsmooth
  obtain ⟨inverseNeighborhood, hinverseNeighborhood, hsmoothOnInverse⟩ :=
    hsmoothInverse.contDiffOn le_rfl (by simp)
  obtain ⟨openNeighborhood, hsubsetNeighborhood, hopenNeighborhood, hmemNeighborhood⟩ :=
    mem_nhds_iff.mp hinverseNeighborhood
  have hclosed : IsClosed (f '' (A \ coordinates.source)) :=
    ((hcompact.diff coordinates.open_source).image_of_continuousOn
      (hcontinuous.mono Set.diff_subset)).isClosed
  have hnotimage : f x ∉ f '' (A \ coordinates.source) := by
    rintro ⟨a, ha, heq⟩
    have hax : a = x := hinjective (hA ha.1) (hA source.mem) heq
    exact ha.2 (hax.symm ▸ hxsource)
  have hmembership : ∀ z ∈ coordinates.target ∩ (f '' (A \ coordinates.source))ᶜ,
      z ∈ f '' A ↔ coordinates.symm z ∈ A := by
    intro z hz
    constructor
    · rintro ⟨a, ha, heq⟩
      have hasource : a ∈ coordinates.source := by
        by_contra houtside
        exact hz.2 ⟨a, ⟨ha, houtside⟩, heq⟩
      have hlocal : coordinates a = z := (hagrees ⟨hA ha, hasource⟩).trans heq
      have hinverseValue : coordinates.symm z = a := by
        rw [← hlocal]
        exact coordinates.left_inv hasource
      exact hinverseValue.symm ▸ ha
    · intro ha
      refine ⟨coordinates.symm z, ha, ?_⟩
      exact (hagrees ⟨hA ha, coordinates.map_target hz.1⟩).symm.trans
        (coordinates.right_inv hz.1)
  have hgradient : HasGradientAt (fun z => source.defining (coordinates.symm z))
      (inverseTranspose extension.derivative source.normal) (f x) := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hsourceDerivative : HasFDerivAt source.defining
        (InnerProductSpace.toDual ℝ E source.normal) (coordinates.symm (f x)) := by
      rw [hinverse]
      exact source.hasGradientAt_defining.hasFDerivAt
    have hchain := hsourceDerivative.comp (f x)
      (coordinates.hasFDerivAt_symm htarget hderivative)
    convert hchain using 1
    ext v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
      inverseTranspose_apply, ContinuousLinearMap.adjoint_inner_left]
  refine ⟨C1BoundaryAt.ofDefiningFunction (f '' A) (f x)
    ((coordinates.target ∩ (f '' (A \ coordinates.source))ᶜ) ∩ openNeighborhood)
    ((coordinates.open_target.inter hclosed.isOpen_compl).inter hopenNeighborhood)
    ⟨⟨htarget, hnotimage⟩, hmemNeighborhood⟩
    (fun z => source.defining (coordinates.symm z)) ?_ ?_ ?_
    (inverseTranspose extension.derivative source.normal) hgradient
    (linearMap_unit_ne_zero (inverseTranspose extension.derivative) source.normal_unit), rfl⟩
  · apply source.contDiffOn_defining.comp
      (hsmoothOnInverse.mono (fun _ hz => hsubsetNeighborhood hz.2))
    intro z hz
    exact (coordinates.map_target hz.1.1).2.2
  · change source.defining (coordinates.symm (f x)) = 0
    rw [hinverse]
    exact source.defining_eq_zero
  · intro z hz
    exact (hmembership z hz.1).trans
      (source.mem_iff _ (coordinates.map_target hz.1.1).2.2)

variable {r s : ℕ}

/-- Image-boundary data with the system's actual canonical differential. -/
theorem SetValuedSystem.exists_imageBoundary
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) (x : E) (source : C1BoundaryAt A x) :
    ∃ target : C1BoundaryAt (system.map '' A) (system.map x),
      target.normal = normalizedLinearMap
        (inverseTranspose (system.derivativeEquiv ⟨x, hA source.mem⟩)) source.normal := by
  exact (Classical.choice (system.diffeomorphism.nonsingular x (hA source.mem))).exists_imageBoundary
    system.map_order_pos hA hcompact
    (system.diffeomorphism.forward_extension.continuousOn.mono hA)
    system.diffeomorphism.injectiveOn source

/-- The normal formula is independent of the image defining function chosen. -/
theorem SetValuedSystem.imageBoundary_normal
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) (x : E) (source : C1BoundaryAt A x)
    (target : C1BoundaryAt (system.map '' A) (system.map x)) :
    target.normal = normalizedLinearMap
      (inverseTranspose (system.derivativeEquiv ⟨x, hA source.mem⟩)) source.normal := by
  obtain ⟨constructed, hnormal⟩ := system.exists_imageBoundary A hA hcompact x source
  exact (target.normal_unique constructed).trans hnormal

/-- Reversing the normal transport recovers the source outward normal. -/
theorem SetValuedSystem.imageBoundary_normal_symm
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) (x : E) (source : C1BoundaryAt A x)
    (target : C1BoundaryAt (system.map '' A) (system.map x)) :
    normalizedLinearMap
      (inverseTranspose (system.derivativeEquiv ⟨x, hA source.mem⟩)).symm target.normal =
      source.normal := by
  rw [system.imageBoundary_normal A hA hcompact x source target]
  exact normalizedLinearMap_symm_apply _ source.normal_unit

/-- The corresponding inward normal is transported with the same differential. -/
theorem SetValuedSystem.imageBoundary_inwardNormal
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) (x : E) (source : C1BoundaryAt A x)
    (target : C1BoundaryAt (system.map '' A) (system.map x)) :
    -target.normal = normalizedLinearMap
      (inverseTranspose (system.derivativeEquiv ⟨x, hA source.mem⟩)) (-source.normal) := by
  rw [system.imageBoundary_normal A hA hcompact x source target]
  simp only [normalizedLinearMap, map_neg, norm_neg, smul_neg]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The original unoriented C1-frontier assumption suffices for normal transport.
Regular closedness supplies the source orientation; no image chart is an input. -/
theorem SetValuedSystem.exists_imageBoundary_of_frontierGraph
    (system : SetValuedSystem (E := E) r s) (A : Set E) (hA : A ⊆ system.domain)
    (hcompact : IsCompact A) (hregular : IsRegularClosed A) (x : E)
    (source : C1FrontierGraphAt (F := F) A x) :
    ∃ target : C1BoundaryAt (system.map '' A) (system.map x),
      target.normal = normalizedLinearMap
        (inverseTranspose (system.derivativeEquiv
          ⟨x, hA (source.toC1BoundaryAt hregular).mem⟩))
        (source.outwardNormal hregular) :=
  system.exists_imageBoundary A hA hcompact x (source.toC1BoundaryAt hregular)

end BoundedUncertainty
