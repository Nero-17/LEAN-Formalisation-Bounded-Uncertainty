import BoundedUncertainty.C1FrontierGraph
import BoundedUncertainty.RelativeHomeomorph
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
An actual half-space atlas on the subtype of a set with a one-sided C1
boundary graph at every frontier point. The atlas is topological: continuity
of the graph extension suffices, and no differentiable atlas is asserted.
-/

namespace BoundedUncertainty

open Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Graph flattening with the domain on the nonnegative side. -/
noncomputable def inwardGraphCoordinatesHomeomorph
    (coordinates : E ≃L[ℝ] ℝ × F) (y : E) (graph : C(F, ℝ)) : E ≃ₜ ℝ × F :=
  (graphCoordinatesHomeomorph coordinates y graph).symm.trans
    ((Homeomorph.neg ℝ).prodCongr (Homeomorph.refl F))

@[simp] theorem inwardGraphCoordinatesHomeomorph_apply
    (coordinates : E ≃L[ℝ] ℝ × F) (y : E) (graph : C(F, ℝ)) (z : E) :
    inwardGraphCoordinatesHomeomorph coordinates y graph z =
      (graph (coordinates (z - y)).2 - (coordinates (z - y)).1,
        (coordinates (z - y)).2) := by
  simp [inwardGraphCoordinatesHomeomorph, neg_sub]

/-- The boundary chart is a local homeomorphism of the actual set subtype
and the actual half-space subtype, with their existing topologies. -/
theorem C1BoundaryGraphAt.exists_halfSpaceChart {B : Set E} {y : E}
    (chart : C1BoundaryGraphAt (F := F) B y) (hy : y ∈ B) :
    ∃ coordinates : OpenPartialHomeomorph B {p : ℝ × F // 0 ≤ p.1},
      (⟨y, hy⟩ : B) ∈ coordinates.source := by
  obtain ⟨extension, radius, hradius, _, hagrees⟩ := exists_continuous_extension_near_zero
    chart.graph chart.graphDomain chart.isOpen_graphDomain chart.zero_mem_graphDomain
    chart.contDiffOn_graph.continuousOn
  have hopen : IsOpen (chart.neighborhood ∩
      (fun z => (chart.coordinates (z - y)).2) ⁻¹' Metric.ball (0 : F) radius) :=
    chart.isOpen_neighborhood.inter (Metric.isOpen_ball.preimage
      (chart.coordinates.continuous.comp (continuous_id.sub continuous_const)).snd)
  have hmem : y ∈ chart.neighborhood ∩
      (fun z => (chart.coordinates (z - y)).2) ⁻¹' Metric.ball (0 : F) radius := by
    exact ⟨chart.mem_neighborhood, by simpa using Metric.mem_ball_self (x := (0 : F)) hradius⟩
  have hsets : ∀ z ∈ chart.neighborhood ∩
      (fun z => (chart.coordinates (z - y)).2) ⁻¹' Metric.ball (0 : F) radius,
      z ∈ B ↔ inwardGraphCoordinatesHomeomorph chart.coordinates y extension z ∈
        {p : ℝ × F | 0 ≤ p.1} := by
    intro z hz
    rw [chart.mem_iff z hz.1, inwardGraphCoordinatesHomeomorph_apply]
    change _ ≤ _ ↔ 0 ≤ extension _ - _
    rw [hagrees hz.2]
    exact sub_nonneg.symm
  refine ⟨relativeOpenPartialHomeomorph
    (inwardGraphCoordinatesHomeomorph chart.coordinates y extension)
    B {p : ℝ × F | 0 ≤ p.1} _ hopen hsets y hy hmem, ?_⟩
  exact hmem

/-- Shifted affine coordinates place an interior point strictly inside the
model half-space. -/
noncomputable def interiorCoordinatesHomeomorph
    (coordinates : E ≃L[ℝ] ℝ × F) (y : E) : E ≃ₜ ℝ × F where
  toFun z := coordinates (z - y) + (1, 0)
  invFun z := coordinates.symm (z - (1, 0)) + y
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := (coordinates.continuous.comp
    (continuous_id.sub continuous_const)).add continuous_const
  continuous_invFun := (coordinates.symm.continuous.comp
    (continuous_id.sub continuous_const)).add continuous_const

/-- Every interior point also has a chart into the same half-space model. -/
theorem exists_interior_halfSpaceChart (coordinates : E ≃L[ℝ] ℝ × F)
    {B : Set E} {y : E} (hy : y ∈ interior B) :
    ∃ chart : OpenPartialHomeomorph B {p : ℝ × F // 0 ≤ p.1},
      (⟨y, interior_subset hy⟩ : B) ∈ chart.source := by
  have hopen : IsOpen (interior B ∩
      {z : E | 0 < (interiorCoordinatesHomeomorph coordinates y z).1}) :=
    isOpen_interior.inter (isOpen_lt continuous_const
      (interiorCoordinatesHomeomorph coordinates y).continuous.fst)
  have hmem : y ∈ interior B ∩
      {z : E | 0 < (interiorCoordinatesHomeomorph coordinates y z).1} := by
    exact ⟨hy, by simp [interiorCoordinatesHomeomorph]⟩
  have hsets : ∀ z ∈ interior B ∩
      {z : E | 0 < (interiorCoordinatesHomeomorph coordinates y z).1},
      z ∈ B ↔ interiorCoordinatesHomeomorph coordinates y z ∈
        {p : ℝ × F | 0 ≤ p.1} := by
    intro z hz
    exact iff_of_true (interior_subset hz.1)
      (show 0 ≤ (interiorCoordinatesHomeomorph coordinates y z).1 from le_of_lt hz.2)
  refine ⟨relativeOpenPartialHomeomorph (interiorCoordinatesHomeomorph coordinates y)
    B {p : ℝ × F | 0 ≤ p.1} _ hopen hsets y (interior_subset hy) hmem, ?_⟩
  exact hmem

/-- The local graph hypotheses provide a half-space chart at every point,
including all interior points. -/
theorem exists_halfSpaceChart (coordinates : E ≃L[ℝ] ℝ × F) (B : Set E)
    (boundary : ∀ y ∈ frontier B, C1BoundaryGraphAt (F := F) B y) (y : B) :
    ∃ chart : OpenPartialHomeomorph B {p : ℝ × F // 0 ≤ p.1}, y ∈ chart.source := by
  by_cases hy : (y : E) ∈ interior B
  · exact exists_interior_halfSpaceChart coordinates hy
  · exact (boundary y ⟨subset_closure y.property, hy⟩).exists_halfSpaceChart y.property

/-- A topological atlas on the actual set subtype. No replacement topology
and no assumed manifold structure enters the construction. -/
noncomputable def boundaryGraphChartedSpace (coordinates : E ≃L[ℝ] ℝ × F) (B : Set E)
    (boundary : ∀ y ∈ frontier B, C1BoundaryGraphAt (F := F) B y) :
    ChartedSpace {p : ℝ × F // 0 ≤ p.1} B where
  atlas := Set.range (fun y : B => (exists_halfSpaceChart coordinates B boundary y).choose)
  chartAt y := (exists_halfSpaceChart coordinates B boundary y).choose
  mem_chart_source y := (exists_halfSpaceChart coordinates B boundary y).choose_spec
  chart_mem_atlas y := ⟨y, rfl⟩

/-- A frontier-only graph family supplies the same actual half-space atlas
when the domain is regular closed. -/
noncomputable def frontierGraphChartedSpace (coordinates : E ≃L[ℝ] ℝ × F) (B : Set E)
    (hregular : IsRegularClosed B)
    (boundary : ∀ y ∈ frontier B, C1FrontierGraphAt (F := F) B y) :
    ChartedSpace {p : ℝ × F // 0 ≤ p.1} B :=
  boundaryGraphChartedSpace coordinates B
    (fun y hy => (boundary y hy).toC1BoundaryGraphAt hregular)

end BoundedUncertainty
