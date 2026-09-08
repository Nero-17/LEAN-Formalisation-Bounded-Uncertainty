import Mathlib.Geometry.Manifold.ChartedSpace

/-! Change the model of an actual charted space through a genuine
homeomorphism. The topology of the space being charted is left fixed. -/

namespace BoundedUncertainty

open Set

noncomputable def chartedSpaceChangeModel {H K M : Type*}
    [TopologicalSpace H] [TopologicalSpace K] [TopologicalSpace M]
    [ChartedSpace H M] (equivalence : H ≃ₜ K) : ChartedSpace K M where
  atlas := range (fun point : M =>
    (chartAt H point).trans equivalence.toOpenPartialHomeomorph)
  chartAt point := (chartAt H point).trans equivalence.toOpenPartialHomeomorph
  mem_chart_source point := by
    simp only [OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact mem_chart_source H point
  chart_mem_atlas point := ⟨point, rfl⟩

end BoundedUncertainty
