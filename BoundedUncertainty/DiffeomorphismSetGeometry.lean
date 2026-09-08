import BoundedUncertainty.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
The set geometry in Notation 3.3. Only local ambient extensions are used.
The image of the whole domain need not be closed. The inverse's relative
continuity prevents other points of the domain from entering an IFT chart.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {order : ℕ} {X A : Set E} {f : E → E} {x : E}

/-- A nonsingular local extension gives an actual local ambient homeomorphism,
agreeing with the given map wherever the source meets its stated domain. -/
theorem NonsingularLocalExtensionAt.exists_openPartialHomeomorph
    (extension : NonsingularLocalExtensionAt order X f x) (horder : 1 ≤ order) :
    ∃ coordinates : OpenPartialHomeomorph E E, x ∈ coordinates.source ∧
      Set.EqOn coordinates f (X ∩ coordinates.source) := by
  have hsmooth : ContDiffAt ℝ 1 extension.extension x :=
    (extension.contDiffOn_extension.of_le (by exact_mod_cast horder)).contDiffAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  refine ⟨(hsmooth.toOpenPartialHomeomorph extension.extension
    extension.hasFDerivAt_extension one_ne_zero).restrOpen
      extension.neighborhood extension.isOpen_neighborhood, ?_, ?_⟩
  · exact ⟨hsmooth.mem_toOpenPartialHomeomorph_source
      extension.hasFDerivAt_extension one_ne_zero, extension.mem_neighborhood⟩
  · intro z hz
    exact extension.agrees ⟨hz.1, hz.2.2⟩

theorem AmbientDiffeomorphismOn.exists_openPartialHomeomorph
    (diffeomorphism : AmbientDiffeomorphismOn order X f) (horder : 1 ≤ order)
    (x : E) (hx : x ∈ X) :
    ∃ coordinates : OpenPartialHomeomorph E E, x ∈ coordinates.source ∧
      Set.EqOn coordinates f (X ∩ coordinates.source) := by
  obtain ⟨extension⟩ := diffeomorphism.nonsingular x hx
  exact extension.exists_openPartialHomeomorph horder

theorem AmbientDiffeomorphismOn.image_interior_subset
    (diffeomorphism : AmbientDiffeomorphismOn order X f) (horder : 1 ≤ order)
    (hA : A ⊆ X) : f '' interior A ⊆ interior (f '' A) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨coordinates, hxsource, hagrees⟩ :=
    diffeomorphism.exists_openPartialHomeomorph horder x (hA (interior_subset hx))
  have hsubset : coordinates '' (coordinates.source ∩ interior A) ⊆ f '' A := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, interior_subset hz.2,
      (hagrees ⟨hA (interior_subset hz.2), hz.1⟩).symm⟩
  exact interior_maximal hsubset (coordinates.isOpen_image_source_inter isOpen_interior)
    ⟨x, ⟨hxsource, hx⟩, hagrees ⟨hA (interior_subset hx), hxsource⟩⟩

/-- Relative continuity of the actual inverse suffices for the reverse interior inclusion. -/
theorem AmbientDiffeomorphismOn.interior_image_subset
    (diffeomorphism : AmbientDiffeomorphismOn order X f) (horder : 1 ≤ order)
    (hA : A ⊆ X) : interior (f '' A) ⊆ f '' interior A := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := interior_subset hz
  obtain ⟨coordinates, hxsource, hagrees⟩ :=
    diffeomorphism.exists_openPartialHomeomorph horder x (hA hx)
  have hcoordinates : coordinates x = f x := hagrees ⟨hA hx, hxsource⟩
  have htarget : f x ∈ coordinates.target :=
    hcoordinates ▸ coordinates.map_source hxsource
  have hinverse : diffeomorphism.inverse (f x) = x := diffeomorphism.left_inverse (hA hx)
  have hpreimage : diffeomorphism.inverse ⁻¹' coordinates.source ∈ 𝓝[f '' X] (f x) := by
    apply (diffeomorphism.inverse_extension.continuousOn (f x) ⟨x, hA hx, rfl⟩).preimage_mem_nhdsWithin
    exact coordinates.open_source.mem_nhds (hinverse.symm ▸ hxsource)
  obtain ⟨neighborhood, hopen, hmem, hcontrol⟩ := mem_nhdsWithin.mp hpreimage
  have himage : coordinates.symm ''
      ((coordinates.target ∩ neighborhood) ∩ interior (f '' A)) ⊆ A := by
    rintro _ ⟨w, hw, rfl⟩
    have hwimage : w ∈ f '' X := (image_mono hA) (interior_subset hw.2)
    have hinverseSource : diffeomorphism.inverse w ∈ coordinates.source :=
      hcontrol ⟨hw.1.2, hwimage⟩
    have hinverseA : diffeomorphism.inverse w ∈ A := by
      obtain ⟨a, ha, rfl⟩ := interior_subset hw.2
      rw [diffeomorphism.left_inverse (hA ha)]
      exact ha
    have hforward : coordinates (diffeomorphism.inverse w) = w :=
      (hagrees ⟨diffeomorphism.inverse_mapsTo hwimage, hinverseSource⟩).trans
        (diffeomorphism.right_inverse hwimage)
    have hlocalInverse : coordinates.symm w = diffeomorphism.inverse w := by
      calc
        coordinates.symm w = coordinates.symm (coordinates (diffeomorphism.inverse w)) :=
          congrArg coordinates.symm hforward.symm
        _ = diffeomorphism.inverse w := coordinates.left_inv hinverseSource
    rw [hlocalInverse]
    exact hinverseA
  refine ⟨x, ?_, rfl⟩
  apply interior_maximal himage
    (coordinates.isOpen_image_symm_of_subset_target
      ((coordinates.open_target.inter hopen).inter isOpen_interior)
      (fun _ hw => hw.1.1))
  refine ⟨f x, ⟨⟨htarget, hmem⟩, hz⟩, ?_⟩
  rw [← hcoordinates]
  exact coordinates.left_inv hxsource

theorem AmbientDiffeomorphismOn.interior_image
    (diffeomorphism : AmbientDiffeomorphismOn order X f) (horder : 1 ≤ order)
    (hA : A ⊆ X) : interior (f '' A) = f '' interior A :=
  Set.Subset.antisymm (diffeomorphism.interior_image_subset horder hA)
    (diffeomorphism.image_interior_subset horder hA)

omit [CompleteSpace E] in
theorem AmbientDiffeomorphismOn.isCompact_image
    (diffeomorphism : AmbientDiffeomorphismOn order X f)
    (hA : A ⊆ X) (hcompact : IsCompact A) : IsCompact (f '' A) :=
  hcompact.image_of_continuousOn (diffeomorphism.forward_extension.continuousOn.mono hA)

theorem AmbientDiffeomorphismOn.isRegularClosed_image
    (diffeomorphism : AmbientDiffeomorphismOn order X f) (horder : 1 ≤ order)
    (hA : A ⊆ X) (hcompact : IsCompact A) (hregular : IsRegularClosed A) :
    IsRegularClosed (f '' A) := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset (diffeomorphism.isCompact_image hA hcompact).isClosed
  · have hcontinuous : ContinuousOn f (closure (interior A)) := by
      rw [hregular]
      exact diffeomorphism.forward_extension.continuousOn.mono hA
    have hclosure := hcontinuous.image_closure
    rw [hregular] at hclosure
    exact hclosure.trans (closure_mono (diffeomorphism.image_interior_subset horder hA))

/-- The frontier formula in Notation 3.3; no closedness of the image of the whole domain is used. -/
theorem AmbientDiffeomorphismOn.frontier_image
    (diffeomorphism : AmbientDiffeomorphismOn order X f) (horder : 1 ≤ order)
    (hA : A ⊆ X) (hcompact : IsCompact A) : frontier (f '' A) = f '' frontier A := by
  rw [(diffeomorphism.isCompact_image hA hcompact).isClosed.frontier_eq,
    hcompact.isClosed.frontier_eq, diffeomorphism.interior_image horder hA]
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
    exact ⟨x, ⟨hx, fun hxinterior => hnot ⟨x, hxinterior, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxnot⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, heq⟩
    have hxy : y = x := diffeomorphism.injectiveOn (hA (interior_subset hy)) (hA hx) heq
    exact hxnot (hxy ▸ hy)

end BoundedUncertainty
