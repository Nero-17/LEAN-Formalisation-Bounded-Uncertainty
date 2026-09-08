import BoundedUncertainty.Basic
import BoundedUncertainty.AmbientDerivative

/-!
Canonical derivatives of the manuscript's locally extendible maps.
The derivative is selected from a smooth local extension, never from the
unrestricted ambient representative or from an unproved within-derivative API.
-/

namespace BoundedUncertainty

open Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def HasLocalExtensionOn.ambientDerivative {order : ℕ}
    {X : Set E} {f : E → F} (h : HasLocalExtensionOn order X f) (x : X) : E →L[ℝ] F :=
  fderiv ℝ (Classical.choice (h x x.property)).extension x

/-- Any local extension gives the same canonical derivative at each domain point
in its open neighborhood. This also allows different finite smoothness orders. -/
theorem HasLocalExtensionOn.ambientDerivative_eq_extension
    {order otherOrder : ℕ} {X : Set E} {f : E → F}
    (h : HasLocalExtensionOn order X f) (hX : IsRegularClosed X)
    (horder : 1 ≤ order) (hotherOrder : 1 ≤ otherOrder)
    {x : E} (extension : LocalExtensionAt otherOrder X f x)
    (y : X) (hy : (y : E) ∈ extension.neighborhood) :
    h.ambientDerivative y = fderiv ℝ extension.extension y := by
  unfold HasLocalExtensionOn.ambientDerivative
  apply fderiv_eq_of_local_ambient_extensions
      (X := X)
      (U := (Classical.choice (h y y.property)).neighborhood)
      (V := extension.neighborhood)
  · intro z hz
    rw [hX]
    exact hz
  · exact (Classical.choice (h y y.property)).isOpen_neighborhood
  · exact extension.isOpen_neighborhood
  · exact (Classical.choice (h y y.property)).contDiffOn_extension.of_le
      (by exact_mod_cast horder)
  · exact extension.contDiffOn_extension.of_le (by exact_mod_cast hotherOrder)
  · intro z hz
    exact ((Classical.choice (h y y.property)).agrees hz.1).trans
      (extension.agrees ⟨hz.1.1, hz.2⟩).symm
  · exact y.property
  · exact (Classical.choice (h y y.property)).mem_neighborhood
  · exact hy

/-- The canonical derivative is continuous on the domain, including its boundary. -/
theorem HasLocalExtensionOn.continuous_ambientDerivative
    {order : ℕ} {X : Set E} {f : E → F}
    (h : HasLocalExtensionOn order X f) (hX : IsRegularClosed X) (horder : 1 ≤ order) :
    Continuous h.ambientDerivative := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨extension⟩ := h x x.property
  have hcontinuous : ContinuousAt (fderiv ℝ extension.extension) (x : E) :=
    (extension.contDiffOn_extension.continuousOn_fderiv_of_isOpen
      extension.isOpen_neighborhood (by exact_mod_cast horder)).continuousAt
      (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)
  apply (hcontinuous.comp continuous_subtype_val.continuousAt).congr
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    (extension.isOpen_neighborhood.mem_nhds extension.mem_neighborhood)] with y hy
  exact (h.ambientDerivative_eq_extension hX horder horder extension y hy).symm

end BoundedUncertainty
