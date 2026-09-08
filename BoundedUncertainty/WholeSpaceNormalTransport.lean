import BoundedUncertainty.BoundaryInverseRepresentation
import BoundedUncertainty.NormalBundleNotation

/-!
Actual whole-space deterministic transport and inward normal pullback.
The preimage defining function is composed with a genuine local extension
of the map, and its gradient is the transpose of the canonical derivative.
No compactness or unproved image-chart assumption is needed.
-/

namespace BoundedUncertainty

open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {r s : ℕ}

/-- In the whole-space self-map case the given map and inverse form a global homeomorphism. -/
noncomputable def SetValuedSystem.wholeSpaceHomeomorph
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) : E ≃ₜ E where
  toFun := system.map
  invFun := system.diffeomorphism.inverse
  left_inv x := system.diffeomorphism.left_inverse (hwhole ▸ mem_univ x)
  right_inv y := system.diffeomorphism.right_inverse ((hself.trans hwhole) ▸ mem_univ y)
  continuous_toFun := continuousOn_univ.mp (hwhole ▸
    system.diffeomorphism.forward_extension.continuousOn)
  continuous_invFun := continuousOn_univ.mp ((hself.trans hwhole) ▸
    system.diffeomorphism.inverse_extension.continuousOn)

omit [CompleteSpace E] in
theorem SetValuedSystem.frontier_preimage_of_wholeSpace
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) (B : Set E) :
    frontier (system.map ⁻¹' B) = system.map ⁻¹' frontier B :=
  ((system.wholeSpaceHomeomorph hwhole hself).preimage_frontier B).symm

omit [CompleteSpace E] in
theorem SetValuedSystem.map_mem_frontier_of_preimage_frontier
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) (B : Set E)
    (x : E) (hx : x ∈ frontier (system.map ⁻¹' B)) : system.map x ∈ frontier B := by
  have hmem : x ∈ system.map ⁻¹' frontier B := by
    rw [← system.frontier_preimage_of_wholeSpace hwhole hself B]
    exact hx
  exact hmem

omit [CompleteSpace E] in
theorem SetValuedSystem.isRegularClosed_preimage_of_wholeSpace
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) (B : Set E)
    (hB : IsRegularClosed B) : IsRegularClosed (system.map ⁻¹' B) := by
  change closure (interior ((system.wholeSpaceHomeomorph hwhole hself) ⁻¹' B)) = _
  rw [← (system.wholeSpaceHomeomorph hwhole hself).preimage_interior,
    ← (system.wholeSpaceHomeomorph hwhole hself).preimage_closure, hB]
  rfl

/-- The actual preimage has C1 boundary data with the transpose normal formula. -/
theorem SetValuedSystem.exists_preimageBoundary_of_wholeSpace
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (B : Set E) (x : E) (target : C1BoundaryAt B (system.map x)) :
    ∃ source : C1BoundaryAt (system.map ⁻¹' B) x,
      source.normal = normalizedLinearMap
        (inverseTranspose (system.derivativeEquiv ⟨x, hwhole ▸ mem_univ x⟩)).symm target.normal := by
  let extension := Classical.choice (system.diffeomorphism.nonsingular x (hwhole ▸ mem_univ x))
  have hsmooth : ContDiffOn ℝ 1 extension.extension extension.neighborhood :=
    extension.contDiffOn_extension.of_le (by exact_mod_cast system.map_order_pos)
  have hvalue : extension.extension x = system.map x :=
    extension.agrees ⟨hwhole ▸ mem_univ x, extension.mem_neighborhood⟩
  have hD : HasFDerivAt extension.extension
      (system.derivativeEquiv ⟨x, hwhole ▸ mem_univ x⟩ : E →L[ℝ] E) x :=
    extension.hasFDerivAt_extension
  have hgradient : HasGradientAt (target.defining ∘ extension.extension)
      ((inverseTranspose (system.derivativeEquiv ⟨x, hwhole ▸ mem_univ x⟩)).symm target.normal) x := by
    have htarget : HasGradientAt target.defining target.normal (extension.extension x) :=
      hvalue.symm ▸ target.hasGradientAt_defining
    rw [hasGradientAt_iff_hasFDerivAt]
    convert htarget.hasFDerivAt.comp x hD using 1
    ext v
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
      inverseTranspose_symm_apply, ContinuousLinearMap.adjoint_inner_left]
  refine ⟨C1BoundaryAt.ofDefiningFunction (system.map ⁻¹' B) x
    (extension.neighborhood ∩ extension.extension ⁻¹' target.neighborhood)
    (hsmooth.continuousOn.isOpen_inter_preimage extension.isOpen_neighborhood
      target.isOpen_neighborhood)
    ⟨extension.mem_neighborhood, by
      change extension.extension x ∈ target.neighborhood
      rw [hvalue]
      exact target.mem_neighborhood⟩
    (target.defining ∘ extension.extension)
    (target.contDiffOn_defining.comp (hsmooth.mono inter_subset_left) (fun _ hw => hw.2))
    ?_ ?_ _ hgradient
    (linearMap_unit_ne_zero _ target.normal_unit), rfl⟩
  · change target.defining (extension.extension x) = 0
    rw [hvalue]
    exact target.defining_eq_zero
  · intro w hw
    change system.map w ∈ B ↔ target.defining (extension.extension w) ≤ 0
    rw [← extension.agrees ⟨hwhole ▸ mem_univ w, hw.1⟩]
    exact target.mem_iff _ hw.2

theorem SetValuedSystem.preimageBoundary_normal_of_wholeSpace
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (B : Set E) (x : E) (target : C1BoundaryAt B (system.map x))
    (source : C1BoundaryAt (system.map ⁻¹' B) x) :
    source.normal = normalizedLinearMap
      (inverseTranspose (system.derivativeEquiv ⟨x, hwhole ▸ mem_univ x⟩)).symm target.normal := by
  obtain ⟨constructed, hnormal⟩ := system.exists_preimageBoundary_of_wholeSpace hwhole B x target
  exact (source.normal_unique constructed).trans hnormal

/-- The actual linear lift carries the actual preimage inward normal to the target inward normal. -/
theorem SetValuedSystem.linearLiftOnAmbient_inward_of_preimageBoundary
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (B : Set E) (x : E) (target : C1BoundaryAt B (system.map x))
    (source : C1BoundaryAt (system.map ⁻¹' B) x) :
    system.linearLiftOnAmbient (x, -source.normal) = (system.map x, -target.normal) := by
  rw [system.linearLiftOnAmbient_apply
    (⟨x, hwhole ▸ mem_univ x⟩, ⟨-source.normal, (norm_neg _).trans source.normal_unit⟩)]
  apply Prod.ext
  · rfl
  change normalizedLinearMap (inverseTranspose (system.derivativeEquiv ⟨x, hwhole ▸ mem_univ x⟩))
    (-source.normal) = -target.normal
  have hneg (T : E ≃L[ℝ] E) (v : E) : normalizedLinearMap T (-v) = -normalizedLinearMap T v := by
    simp only [normalizedLinearMap, map_neg, norm_neg, smul_neg]
  rw [hneg, system.preimageBoundary_normal_of_wholeSpace hwhole B x target source,
    normalizedLinearMap_apply_symm _ target.normal_unit]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem SetValuedSystem.linearLiftOnAmbient_inwardNormalPair_preimage
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) (B : Set E)
    (hB : IsRegularClosed B) (hpreimage : IsRegularClosed (system.map ⁻¹' B))
    (target : (y : frontier B) → C1FrontierGraphAt (F := F) B y)
    (source : (x : frontier (system.map ⁻¹' B)) →
      C1FrontierGraphAt (F := G) (system.map ⁻¹' B) x)
    (x : frontier (system.map ⁻¹' B)) :
    system.linearLiftOnAmbient (inwardNormalPair (system.map ⁻¹' B) hpreimage source x) =
      inwardNormalPair B hB target
        ⟨system.map x, system.map_mem_frontier_of_preimage_frontier hwhole hself B x x.property⟩ := by
  exact system.linearLiftOnAmbient_inward_of_preimageBoundary hwhole B x
    ((target ⟨system.map x,
      system.map_mem_frontier_of_preimage_frontier hwhole hself B x x.property⟩).toC1BoundaryAt hB)
    ((source x).toC1BoundaryAt hpreimage)

/-- The actual linear lift maps the entire actual preimage inward bundle onto the target bundle. -/
theorem SetValuedSystem.image_linearLiftOnAmbient_inwardNormalBundle_preimage
    (system : SetValuedSystem (E := E) r s) (hwhole : system.domain = univ)
    (hself : system.map '' system.domain = system.domain) (B : Set E)
    (hB : IsRegularClosed B) (hpreimage : IsRegularClosed (system.map ⁻¹' B))
    (target : (y : frontier B) → C1FrontierGraphAt (F := F) B y)
    (source : (x : frontier (system.map ⁻¹' B)) →
      C1FrontierGraphAt (F := G) (system.map ⁻¹' B) x) :
    system.linearLiftOnAmbient '' inwardNormalBundle (system.map ⁻¹' B) hpreimage source =
      inwardNormalBundle B hB target := by
  apply Subset.antisymm
  · rintro p ⟨q, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, (system.linearLiftOnAmbient_inwardNormalPair_preimage hwhole hself B hB
      hpreimage target source x).symm⟩
  · rintro p ⟨y, rfl⟩
    obtain ⟨x, hxy⟩ := (system.wholeSpaceHomeomorph hwhole hself).surjective (y : E)
    change system.map x = (y : E) at hxy
    have hx : x ∈ frontier (system.map ⁻¹' B) := by
      rw [system.frontier_preimage_of_wholeSpace hwhole hself B]
      change system.map x ∈ frontier B
      rw [hxy]
      exact y.property
    refine ⟨inwardNormalPair (system.map ⁻¹' B) hpreimage source ⟨x, hx⟩,
      ⟨⟨x, hx⟩, rfl⟩, ?_⟩
    have hindex : (⟨system.map x,
        system.map_mem_frontier_of_preimage_frontier hwhole hself B x hx⟩ : frontier B) = y :=
      Subtype.ext hxy
    simpa only [hindex] using system.linearLiftOnAmbient_inwardNormalPair_preimage
      hwhole hself B hB hpreimage target source ⟨x, hx⟩

end BoundedUncertainty
