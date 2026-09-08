import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Tactic.Linarith

/-! An elementary one-dimensional invariance-of-domain statement, obtained
from monotonicity and the intermediate value theorem. This is a concrete
low-dimensional route to projection openness, not the general-dimensional
topological theorem required by standalone Lemma 4.8. -/

namespace BoundedUncertainty

open Set Topology

/-- A continuous injective real function sends any open domain to an open set. -/
theorem isOpen_image_real_of_continuousOn_injOn (domain : Set ℝ) (function : ℝ → ℝ)
    (hopen : IsOpen domain) (hcontinuous : ContinuousOn function domain)
    (hinjective : InjOn function domain) : IsOpen (function '' domain) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨point, hpoint, rfl⟩
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpoint)
  have hinterval : Icc (point - radius / 2) (point + radius / 2) ⊆ domain := by
    intro value hvalue
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hvalue.1, hvalue.2]
  have horder : point - radius / 2 ≤ point + radius / 2 := by linarith
  have hleft : point - radius / 2 < point := by linarith
  have hright : point < point + radius / 2 := by linarith
  have hmiddle : point ∈ Icc (point - radius / 2) (point + radius / 2) :=
    ⟨hleft.le, hright.le⟩
  have hrestricted := hcontinuous.mono hinterval
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' horder hrestricted
      (hinjective.mono hinterval) with hincreasing | hdecreasing
  · apply Filter.mem_of_superset
      (Ioo_mem_nhds (hincreasing (left_mem_Icc.mpr horder) hmiddle hleft)
        (hincreasing hmiddle (right_mem_Icc.mpr horder) hright))
    exact fun value hvalue => image_mono hinterval
      (intermediate_value_Icc horder hrestricted ⟨hvalue.1.le, hvalue.2.le⟩)
  · apply Filter.mem_of_superset
      (Ioo_mem_nhds (hdecreasing hmiddle (right_mem_Icc.mpr horder) hright)
        (hdecreasing (left_mem_Icc.mpr horder) hmiddle hleft))
    exact fun value hvalue => image_mono hinterval
      (intermediate_value_Icc' horder hrestricted ⟨hvalue.1.le, hvalue.2.le⟩)

/-- The same theorem as an actual open map on the original open subtype domain. -/
theorem isOpenMap_real_subtype_of_continuous_injective (domain : Set ℝ)
    (hopen : IsOpen domain) (function : domain → ℝ)
    (hcontinuous : Continuous function) (hinjective : Function.Injective function) :
    IsOpenMap function := by
  classical
  intro subset hsubset
  let extension : ℝ → ℝ := fun point => if hpoint : point ∈ domain then
    function ⟨point, hpoint⟩ else 0
  have hextension : ∀ point : domain, extension point = function point := by
    intro point
    simp only [extension, dif_pos point.property]
  have hcontinuousOn : ContinuousOn extension domain := by
    rw [continuousOn_iff_continuous_restrict]
    exact hcontinuous.congr (fun point => (hextension point).symm)
  have hinjOn : InjOn extension domain := by
    intro first hfirst second hsecond hequal
    have hequal' : function ⟨first, hfirst⟩ = function ⟨second, hsecond⟩ := by
      simpa only [extension, dif_pos hfirst, dif_pos hsecond] using hequal
    exact congrArg Subtype.val (hinjective hequal')
  have hsub : Subtype.val '' subset ⊆ domain := by
    rintro point ⟨value, _, rfl⟩
    exact value.property
  have hresult := isOpen_image_real_of_continuousOn_injOn (Subtype.val '' subset) extension
    (hopen.isOpenMap_subtype_val subset hsubset) (hcontinuousOn.mono hsub) (hinjOn.mono hsub)
  convert hresult using 1
  rw [image_image]
  exact image_congr (fun point _ => (hextension point).symm)

/-- Invariance of domain on a one-dimensional manifold, with local injectivity
and the actual existing charted topology. -/
theorem isOpenMap_of_real_charts_of_locally_injective {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℝ M] (function : M → ℝ)
    (hcontinuous : Continuous function)
    (hlocal : ∀ point : M, ∃ neighborhood : Set M,
      IsOpen neighborhood ∧ point ∈ neighborhood ∧ InjOn function neighborhood) :
    IsOpenMap function := by
  intro subset hopen
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨point, hpoint, rfl⟩
  obtain ⟨neighborhood, hneighborhood, hpointNeighborhood, hinjective⟩ := hlocal point
  have htarget : IsOpen ((chartAt ℝ point).target ∩
      (chartAt ℝ point).symm ⁻¹' (subset ∩ neighborhood)) :=
    (chartAt ℝ point).isOpen_inter_preimage_symm (hopen.inter hneighborhood)
  have hcomposed : ContinuousOn (function ∘ (chartAt ℝ point).symm)
      ((chartAt ℝ point).target ∩ (chartAt ℝ point).symm ⁻¹' (subset ∩ neighborhood)) :=
    hcontinuous.comp_continuousOn ((chartAt ℝ point).continuousOn_symm.mono inter_subset_left)
  have hinj : InjOn (function ∘ (chartAt ℝ point).symm)
      ((chartAt ℝ point).target ∩ (chartAt ℝ point).symm ⁻¹' (subset ∩ neighborhood)) := by
    intro first hfirst second hsecond hequal
    exact (chartAt ℝ point).symm.injOn hfirst.1 hsecond.1
      (hinjective hfirst.2.2 hsecond.2.2 hequal)
  have himage := isOpen_image_real_of_continuousOn_injOn _ _ htarget hcomposed hinj
  have hmember : function point ∈ (function ∘ (chartAt ℝ point).symm) ''
      ((chartAt ℝ point).target ∩ (chartAt ℝ point).symm ⁻¹' (subset ∩ neighborhood)) := by
    refine ⟨chartAt ℝ point point, ⟨mem_chart_target ℝ point, ?_⟩, ?_⟩
    · simpa only [Set.mem_preimage, (chartAt ℝ point).left_inv (mem_chart_source ℝ point)] using
        (show point ∈ subset ∩ neighborhood from ⟨hpoint, hpointNeighborhood⟩)
    · simp only [Function.comp_apply, (chartAt ℝ point).left_inv (mem_chart_source ℝ point)]
  apply Filter.mem_of_superset (himage.mem_nhds hmember)
  rintro value ⟨coordinate, hcoordinate, rfl⟩
  exact ⟨(chartAt ℝ point).symm coordinate, hcoordinate.2.1, rfl⟩

end BoundedUncertainty
