import BoundedUncertainty.VendorBrouwer
import BoundedUncertainty.ChartProjectionOpenness

/-! Invariance of domain with its fixed-point prerequisite proved from the
cubical Sperner theorem. No topological theorem is introduced as an axiom. -/

namespace BoundedUncertainty

open Set Topology

/-- The unit-ball fixed-point interface, discharged by the proved compact
convex Brouwer theorem. -/
theorem brouwerFixedPoint_proved (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : BrouwerFixedPoint E := by
  constructor
  intro function hcontinuous
  exact Vendor.brouwer_fixed_point (Metric.closedBall (0 : E) 1)
    (convex_closedBall (0 : E) 1) (isCompact_closedBall (0 : E) 1)
    ⟨0, by simp⟩ ⟨function, hcontinuous⟩

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The open-image form of invariance of domain in every finite dimension. -/
theorem isOpen_image_of_continuousOn_injOn (function : E → E) (domain : Set E)
    (hopen : IsOpen domain) (hcontinuous : ContinuousOn function domain)
    (hinjective : InjOn function domain) : IsOpen (function '' domain) :=
  invariance_of_domain_open_map (brouwerFixedPoint_proved E) function domain hopen hcontinuous hinjective

/-- An injective restriction of a continuous map from a manifold to its
Euclidean model is open, using the manifold's original topology. -/
theorem isOpenMap_restrict_of_continuous_injOn [TopologicalSpace M] [ChartedSpace E M]
    (function : M → E) (domain : Set M) (hopen : IsOpen domain)
    (hcontinuous : Continuous function) (hinjective : InjOn function domain) :
    IsOpenMap (fun point : domain => function point) :=
  isOpenMap_restrict_of_charts_of_injOn (brouwerFixedPoint_proved E)
    function domain hopen hcontinuous hinjective

end BoundedUncertainty
