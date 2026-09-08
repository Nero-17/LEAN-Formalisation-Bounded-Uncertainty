import BoundedUncertainty.LocalBoundary

/-!
# From a one-sided local C1 graph to normalized boundary data

The graph description contains no normal and imposes no vanishing derivative
on the graph. A transverse coordinate derivative proves that its defining
function has nonzero gradient. The regular-level-set normalization then gives
`C1BoundaryAt`.

This is the graph-to-defining-function bridge. It does not by itself prove
that every regular closed set with a C1 hypersurface frontier has a one-sided
local graph description.
-/

namespace BoundedUncertainty

open Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A one-sided local C1 graph in linear coordinates centred at the marked point. -/
structure C1BoundaryGraphAt (B : Set E) (y : E) where
  coordinates : E ≃L[ℝ] ℝ × F
  neighborhood : Set E
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : y ∈ neighborhood
  graphDomain : Set F
  isOpen_graphDomain : IsOpen graphDomain
  zero_mem_graphDomain : (0 : F) ∈ graphDomain
  graph : F → ℝ
  contDiffOn_graph : ContDiffOn ℝ 1 graph graphDomain
  graph_zero : graph 0 = 0
  mem_iff : ∀ z ∈ neighborhood,
    z ∈ B ↔ (coordinates (z - y)).1 ≤ graph (coordinates (z - y)).2

variable {B : Set E} {y : E}

def C1BoundaryGraphAt.defining (chart : C1BoundaryGraphAt (F := F) B y) : E → ℝ :=
  fun z => (chart.coordinates (z - y)).1 - chart.graph (chart.coordinates (z - y)).2

/-- Restrict the ambient neighbourhood so that the graph is evaluated in its smooth domain. -/
def C1BoundaryGraphAt.definingNeighborhood (chart : C1BoundaryGraphAt (F := F) B y) : Set E :=
  chart.neighborhood ∩ (fun z => (chart.coordinates (z - y)).2) ⁻¹' chart.graphDomain

theorem C1BoundaryGraphAt.isOpen_definingNeighborhood (chart : C1BoundaryGraphAt (F := F) B y) :
    IsOpen chart.definingNeighborhood :=
  chart.isOpen_neighborhood.inter (chart.isOpen_graphDomain.preimage
    ((chart.coordinates.continuous.comp (continuous_id.sub continuous_const)).snd))

theorem C1BoundaryGraphAt.mem_definingNeighborhood (chart : C1BoundaryGraphAt (F := F) B y) :
    y ∈ chart.definingNeighborhood := by
  refine ⟨chart.mem_neighborhood, ?_⟩
  simpa using chart.zero_mem_graphDomain

theorem C1BoundaryGraphAt.contDiffOn_defining (chart : C1BoundaryGraphAt (F := F) B y) :
    ContDiffOn ℝ 1 chart.defining chart.definingNeighborhood := by
  have hcoordinates : ContDiff ℝ 1 (fun z : E => chart.coordinates (z - y)) :=
    chart.coordinates.contDiff.comp (contDiff_id.sub contDiff_const)
  exact hcoordinates.fst.contDiffOn.sub
    (chart.contDiffOn_graph.comp hcoordinates.snd.contDiffOn (fun _ hz => hz.2))

theorem C1BoundaryGraphAt.defining_eq_zero (chart : C1BoundaryGraphAt (F := F) B y) :
    chart.defining y = 0 := by
  simp [C1BoundaryGraphAt.defining, chart.graph_zero]

theorem C1BoundaryGraphAt.mem_iff_defining_nonpos (chart : C1BoundaryGraphAt (F := F) B y)
    (z : E) (hz : z ∈ chart.definingNeighborhood) : z ∈ B ↔ chart.defining z ≤ 0 := by
  simpa only [C1BoundaryGraphAt.defining, sub_nonpos] using chart.mem_iff z hz.1

theorem C1BoundaryGraphAt.hasFDerivAt_defining (chart : C1BoundaryGraphAt (F := F) B y) :
    HasFDerivAt chart.defining
      ((ContinuousLinearMap.fst ℝ ℝ F).comp chart.coordinates.toContinuousLinearMap -
        (fderiv ℝ chart.graph 0).comp
          ((ContinuousLinearMap.snd ℝ ℝ F).comp chart.coordinates.toContinuousLinearMap)) y := by
  have hcoordinates := chart.coordinates.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const y)
  have hgraph : HasFDerivAt chart.graph (fderiv ℝ chart.graph 0)
      (chart.coordinates (y - y)).2 := by
    simpa using (chart.contDiffOn_graph.differentiableOn_one.differentiableAt
      (chart.isOpen_graphDomain.mem_nhds chart.zero_mem_graphDomain)).hasFDerivAt
  simpa only [C1BoundaryGraphAt.defining, ContinuousLinearMap.comp_id] using
    hcoordinates.fst.sub (hgraph.comp y hcoordinates.snd)

/-- The transverse derivative is exactly one, irrespective of the graph's derivative. -/
theorem C1BoundaryGraphAt.fderiv_defining_transverse (chart : C1BoundaryGraphAt (F := F) B y) :
    (fderiv ℝ chart.defining y) (chart.coordinates.symm (1, 0)) = 1 := by
  rw [chart.hasFDerivAt_defining.fderiv]
  simp

variable [CompleteSpace E]

theorem C1BoundaryGraphAt.hasGradientAt_defining (chart : C1BoundaryGraphAt (F := F) B y) :
    HasGradientAt chart.defining (gradient chart.defining y) y :=
  chart.hasFDerivAt_defining.differentiableAt.hasGradientAt

theorem C1BoundaryGraphAt.gradient_defining_ne_zero (chart : C1BoundaryGraphAt (F := F) B y) :
    gradient chart.defining y ≠ 0 := by
  intro hzero
  have heval := chart.fderiv_defining_transverse
  rw [chart.hasGradientAt_defining.fderiv_apply, hzero, inner_zero_left] at heval
  exact zero_ne_one heval

/-- A one-sided C1 graph gives actual normalized defining-function boundary data. -/
noncomputable def C1BoundaryGraphAt.toC1BoundaryAt (chart : C1BoundaryGraphAt (F := F) B y) :
    C1BoundaryAt B y :=
  C1BoundaryAt.ofDefiningFunction B y chart.definingNeighborhood
    chart.isOpen_definingNeighborhood chart.mem_definingNeighborhood chart.defining
    chart.contDiffOn_defining chart.defining_eq_zero chart.mem_iff_defining_nonpos
    (gradient chart.defining y) chart.hasGradientAt_defining chart.gradient_defining_ne_zero

theorem C1BoundaryGraphAt.toC1BoundaryAt_normal (chart : C1BoundaryGraphAt (F := F) B y) :
    chart.toC1BoundaryAt.normal = ‖gradient chart.defining y‖⁻¹ • gradient chart.defining y :=
  rfl

end BoundedUncertainty
