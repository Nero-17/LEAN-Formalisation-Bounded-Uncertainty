import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Topology.Separation.Hausdorff

/-!
# Independence of the derivative from a local ambient extension

For a set contained in the closure of its interior, two `C¹` ambient extensions
that agree on the set have equal derivatives there. Only local smoothness on
open neighborhoods is required. In particular, this does not assume a
`UniqueDiffWithinAt` hypothesis on the original set or a global smooth extension.
-/

namespace BoundedUncertainty

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Equality of two local `C¹` ambient extensions determines their derivative
on every point of a set contained in the closure of its interior. -/
theorem eqOn_fderiv_of_contDiffOn_eqOn {X U : Set E} {f g : E → F}
    (hX : X ⊆ closure (interior X)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hfg : EqOn f g (X ∩ U)) :
    EqOn (fderiv ℝ f) (fderiv ℝ g) (X ∩ U) := by
  have hfgInterior : EqOn f g (interior X ∩ U) :=
    fun _ h => hfg ⟨interior_subset h.1, h.2⟩
  have hderivInterior : EqOn (fderiv ℝ f) (fderiv ℝ g) (interior X ∩ U) := by
    intro y hy
    exact (hfgInterior.eventuallyEq_of_mem
      ((isOpen_interior.inter hU).mem_nhds hy)).fderiv_eq
  exact hderivInterior.of_subset_closure
    ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono inter_subset_right)
    ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).mono inter_subset_right)
    (fun _ h => ⟨interior_subset h.1, h.2⟩)
    (fun _ h => hU.closure_inter ⟨hX h.1, h.2⟩)

/-- Pointwise form of derivative independence on a common open neighborhood. -/
theorem fderiv_eq_of_contDiffOn_eqOn {X U : Set E} {f g : E → F} {x : E}
    (hX : X ⊆ closure (interior X)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hfg : EqOn f g (X ∩ U)) (hxX : x ∈ X) (hxU : x ∈ U) :
    fderiv ℝ f x = fderiv ℝ g x :=
  eqOn_fderiv_of_contDiffOn_eqOn hX hU hf hg hfg ⟨hxX, hxU⟩

/-- Two extensions may be given on different open neighborhoods. Their
derivatives agree wherever both neighborhoods meet the original set. -/
theorem fderiv_eq_of_local_ambient_extensions {X U V : Set E} {f g : E → F} {x : E}
    (hX : X ⊆ closure (interior X)) (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g V)
    (hfg : EqOn f g (X ∩ U ∩ V))
    (hxX : x ∈ X) (hxU : x ∈ U) (hxV : x ∈ V) :
    fderiv ℝ f x = fderiv ℝ g x := by
  exact fderiv_eq_of_contDiffOn_eqOn hX (hU.inter hV)
    (hf.mono inter_subset_left) (hg.mono inter_subset_right)
    (fun _ h => hfg ⟨⟨h.1, h.2.1⟩, h.2.2⟩) hxX ⟨hxU, hxV⟩

end BoundedUncertainty
