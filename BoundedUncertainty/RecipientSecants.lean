import BoundedUncertainty.RecipientParametrization
import BoundedUncertainty.ZeroRadiusSecantLimit

/-!
Theorem 4.9's actual two-moving-recipient secant limit. Gamma inverse supplies
the centres and the genuine boundary map supplies the normals. The positive
radius case uses the two contributing balls; the zero-radius case uses strict
source tangent flatness and the quantitative radius/chord argument.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- Actual Gamma-derived normals are perpendicular to every limiting recipient secant.
The input boundary is C1; no regularity of the recipient boundary is assumed. -/
theorem SetValuedSystem.tendsto_recipient_secants
    (system : SetValuedSystem (E := E) r s) (hcontraction : system.IsContraction)
    (A : Set E) (hA : A ⊆ system.domain) (hcompact : IsCompact A)
    (source : (x : frontier A) → C1BoundaryAt A x)
    (hinjective : Function.Injective (system.boundaryProjection A hA source))
    (hrange : range (system.boundaryProjection A hA source) =
      frontier (setValuedImage system.map system.radius A))
    (point : frontier (setValuedImage system.map system.radius A))
    (first second : ℕ → frontier (setValuedImage system.map system.radius A))
    (hfirst : Tendsto first atTop (𝓝 point))
    (hsecond : Tendsto second atTop (𝓝 point)) :
    Tendsto (fun k =>
      |inner ℝ (system.recipientNormal hcontraction A hA hcompact source hinjective hrange point)
        ((second k : E) - (first k : E))| / ‖(second k : E) - (first k : E)‖)
      atTop (𝓝 0) := by
  have himage : system.map '' A ⊆ system.domain := by
    rintro y ⟨x, hx, rfl⟩
    exact system.map_into_domain (hA hx)
  have hcenterDomain : ∀ z, system.recipientCenter hcontraction A hA hcompact source hinjective hrange z
      ∈ system.domain := fun z => himage
        (system.recipientCenter_mem_image hcontraction A hA hcompact source hinjective hrange z)
  have hcontinuousCenter := system.continuous_recipientCenter
    hcontraction A hA hcompact source hinjective hrange
  have hcontinuousNormal := system.continuous_recipientNormal
    hcontraction A hA hcompact source hinjective hrange
  have hcontinuousRadius : Continuous (fun z => system.radius
      (system.recipientCenter hcontraction A hA hcompact source hinjective hrange z)) := by
    have hrestricted : Continuous (fun y : system.domain => system.radius y) :=
      continuousOn_iff_continuous_restrict.mp system.radius_extension.continuousOn
    exact hrestricted.comp (hcontinuousCenter.subtype_mk hcenterDomain)
  have hfirstFrontier : ∀ k, (first k : E) ∈
      frontier (inflation system.radius (system.map '' A)) := by
    intro k
    simpa only [setValuedImage_eq_inflation] using (first k).property
  have hsecondFrontier : ∀ k, (second k : E) ∈
      frontier (inflation system.radius (system.map '' A)) := by
    intro k
    simpa only [setValuedImage_eq_inflation] using (second k).property
  by_cases hpositive : 0 < system.radius
      (system.recipientCenter hcontraction A hA hcompact source hinjective hrange point)
  · apply tendsto_normalized_secant_of_positive_radius system.radius (system.map '' A)
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (second k))
      (fun k => (first k : E)) (fun k => (second k : E))
      (fun k => system.recipientNormal hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientNormal hcontraction A hA hcompact source hinjective hrange (second k))
      point _ _ hpositive
      (fun k => system.recipientCenter_mem_image hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientCenter_mem_image hcontraction A hA hcompact source hinjective hrange (second k))
      hfirstFrontier hsecondFrontier
      (fun k => system.norm_recipientNormal hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.norm_recipientNormal hcontraction A hA hcompact source hinjective hrange (second k))
      (fun k => system.recipient_radial_position hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipient_radial_position hcontraction A hA hcompact source hinjective hrange (second k))
      (continuous_subtype_val.tendsto point |>.comp hfirst)
      (continuous_subtype_val.tendsto point |>.comp hsecond)
      (hcontinuousRadius.tendsto point |>.comp hfirst)
      (hcontinuousRadius.tendsto point |>.comp hsecond)
      (hcontinuousNormal.tendsto point |>.comp hfirst)
      (hcontinuousNormal.tendsto point |>.comp hsecond)
  · have hzero : system.radius
        (system.recipientCenter hcontraction A hA hcompact source hinjective hrange point) = 0 :=
      le_antisymm (le_of_not_gt hpositive) (system.radius_nonneg _ (hcenterDomain point))
    obtain ⟨boundary, _⟩ := system.exists_imageBoundary A hA hcompact
      (system.recipientSource hcontraction A hA hcompact source hinjective hrange point) (source _)
    have hnormal := system.recipientNormal_eq_imageBoundary_normal_at_zero
      hcontraction A hA hcompact source hinjective hrange point boundary hzero
    have hclosed : IsClosed (system.map '' A) :=
      (system.diffeomorphism.isCompact_image hA hcompact).isClosed
    have hsourceNormal := boundary.isLittleO_normal_chord hclosed
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (second k))
      (hcontinuousCenter.tendsto point |>.comp hfirst)
      (hcontinuousCenter.tendsto point |>.comp hsecond)
      (fun k => system.recipientCenter_mem_frontier_image hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientCenter_mem_frontier_image hcontraction A hA hcompact source hinjective hrange (second k))
    rw [← hnormal] at hsourceNormal
    have hsourceRadius := system.isLittleO_radius_difference_at_zero (system.map '' A) himage
      hclosed _ boundary hzero
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (second k))
      (hcontinuousCenter.tendsto point |>.comp hfirst)
      (hcontinuousCenter.tendsto point |>.comp hsecond)
      (fun k => system.recipientCenter_mem_frontier_image hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientCenter_mem_frontier_image hcontraction A hA hcompact source hinjective hrange (second k))
    apply tendsto_normalized_secant_of_source_flatness
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientCenter hcontraction A hA hcompact source hinjective hrange (second k))
      (fun k => (first k : E)) (fun k => (second k : E))
      (fun k => system.recipientNormal hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipientNormal hcontraction A hA hcompact source hinjective hrange (second k))
      (fun k => system.radius (system.recipientCenter hcontraction A hA hcompact source hinjective hrange (first k)))
      (fun k => system.radius (system.recipientCenter hcontraction A hA hcompact source hinjective hrange (second k))) _
      (fun k => system.radius_nonneg _ (hcenterDomain (first k)))
      (fun k => system.radius_nonneg _ (hcenterDomain (second k)))
      (fun k => system.norm_recipientNormal hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.norm_recipientNormal hcontraction A hA hcompact source hinjective hrange (second k))
      (system.norm_recipientNormal hcontraction A hA hcompact source hinjective hrange point)
      (fun k => system.recipient_radial_position hcontraction A hA hcompact source hinjective hrange (first k))
      (fun k => system.recipient_radial_position hcontraction A hA hcompact source hinjective hrange (second k))
      _ _ hsourceNormal hsourceRadius
      (hcontinuousNormal.tendsto point |>.comp hfirst)
      (hcontinuousNormal.tendsto point |>.comp hsecond)
    · intro k
      simpa only [dist_eq_norm] using radius_le_dist_of_mem_frontier_inflation
        system.radius (system.map '' A) (second k) (hsecondFrontier k)
        (system.recipientCenter hcontraction A hA hcompact source hinjective hrange (first k))
        (system.recipientCenter_mem_image hcontraction A hA hcompact source hinjective hrange (first k))
    · intro k
      simpa only [dist_eq_norm] using radius_le_dist_of_mem_frontier_inflation
        system.radius (system.map '' A) (first k) (hfirstFrontier k)
        (system.recipientCenter hcontraction A hA hcompact source hinjective hrange (second k))
        (system.recipientCenter_mem_image hcontraction A hA hcompact source hinjective hrange (second k))

end BoundedUncertainty
