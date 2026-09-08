import BoundedUncertainty.InvarianceOfDomainFromBrouwer
import Mathlib.Geometry.Manifold.ChartedSpace

/-! Open images of locally injective maps on actual manifold charts. The
explicit Brouwer interface is discharged by the separate proved foundation. -/

namespace BoundedUncertainty

open Set Topology

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]

theorem isOpen_image_of_charts_of_injOn (brouwer : BrouwerFixedPoint E)
    (function : M → E) (domain : Set M) (hopen : IsOpen domain)
    (hcontinuous : Continuous function) (hinjective : InjOn function domain) :
    IsOpen (function '' domain) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨point, hpoint, rfl⟩
  have htarget : IsOpen ((chartAt E point).target ∩
      (chartAt E point).symm ⁻¹' domain) :=
    (chartAt E point).isOpen_inter_preimage_symm hopen
  have hcomposed : ContinuousOn (function ∘ (chartAt E point).symm)
      ((chartAt E point).target ∩ (chartAt E point).symm ⁻¹' domain) :=
    hcontinuous.comp_continuousOn ((chartAt E point).continuousOn_symm.mono inter_subset_left)
  have hinj : InjOn (function ∘ (chartAt E point).symm)
      ((chartAt E point).target ∩ (chartAt E point).symm ⁻¹' domain) := by
    intro first hfirst second hsecond hequal
    exact (chartAt E point).symm.injOn hfirst.1 hsecond.1
      (hinjective hfirst.2 hsecond.2 hequal)
  have himage := invariance_of_domain_open_map brouwer _ _ htarget hcomposed hinj
  have hmember : function point ∈ (function ∘ (chartAt E point).symm) ''
      ((chartAt E point).target ∩ (chartAt E point).symm ⁻¹' domain) := by
    refine ⟨chartAt E point point, ⟨mem_chart_target E point, ?_⟩, ?_⟩
    · simpa only [Set.mem_preimage, (chartAt E point).left_inv (mem_chart_source E point)] using hpoint
    · simp only [Function.comp_apply, (chartAt E point).left_inv (mem_chart_source E point)]
  apply Filter.mem_of_superset (himage.mem_nhds hmember)
  rintro value ⟨coordinate, hcoordinate, rfl⟩
  exact ⟨(chartAt E point).symm coordinate, hcoordinate.2, rfl⟩

theorem isOpenMap_restrict_of_charts_of_injOn (brouwer : BrouwerFixedPoint E)
    (function : M → E) (domain : Set M) (hopen : IsOpen domain)
    (hcontinuous : Continuous function) (hinjective : InjOn function domain) :
    IsOpenMap (fun point : domain => function point) := by
  intro subset hsubset
  have hsub : Subtype.val '' subset ⊆ domain := by
    rintro point ⟨value, _, rfl⟩
    exact value.property
  have hresult := isOpen_image_of_charts_of_injOn brouwer function (Subtype.val '' subset)
    (hopen.isOpenMap_subtype_val subset hsubset) hcontinuous (hinjective.mono hsub)
  simpa only [image_image] using hresult

end BoundedUncertainty
