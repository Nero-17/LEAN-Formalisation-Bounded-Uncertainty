import BoundedUncertainty.C1FrontierContact
import BoundedUncertainty.Section3Interfaces

/-! The outward/inward pairs and normal bundles of Notation 3.3. -/
namespace BoundedUncertainty
open Set
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def outwardNormalPair (B : Set E) (hB : IsRegularClosed B)
    (charts : (x : frontier B) → C1FrontierGraphAt (F := F) B x) (x : frontier B) : E × E :=
  (x, (charts x).outwardNormal hB)

noncomputable def inwardNormalPair (B : Set E) (hB : IsRegularClosed B)
    (charts : (x : frontier B) → C1FrontierGraphAt (F := F) B x) (x : frontier B) : E × E :=
  (x, -(charts x).outwardNormal hB)

noncomputable def outwardNormalBundle (B : Set E) (hB : IsRegularClosed B)
    (charts : (x : frontier B) → C1FrontierGraphAt (F := F) B x) : Set (E × E) :=
  range (outwardNormalPair B hB charts)

noncomputable def inwardNormalBundle (B : Set E) (hB : IsRegularClosed B)
    (charts : (x : frontier B) → C1FrontierGraphAt (F := F) B x) : Set (E × E) :=
  range (inwardNormalPair B hB charts)

theorem outwardNormalBundle_subset (B : Set E) (hB : IsRegularClosed B)
    (charts : (x : frontier B) → C1FrontierGraphAt (F := F) B x) :
    outwardNormalBundle B hB charts ⊆ frontier B ×ˢ {n : E | ‖n‖ = 1} := by
  rintro p ⟨x, rfl⟩
  exact ⟨x.property, (charts x).norm_outwardNormal hB⟩

theorem inwardNormalBundle_subset (B : Set E) (hB : IsRegularClosed B)
    (charts : (x : frontier B) → C1FrontierGraphAt (F := F) B x) :
    inwardNormalBundle B hB charts ⊆ frontier B ×ˢ {n : E | ‖n‖ = 1} := by
  rintro p ⟨x, rfl⟩
  refine ⟨x.property, ?_⟩
  exact (norm_neg _).trans ((charts x).norm_outwardNormal hB)

theorem outwardNormalPair_independent (B : Set E) (hB : IsRegularClosed B)
    (first : (x : frontier B) → C1FrontierGraphAt (F := F) B x)
    (second : (x : frontier B) → C1FrontierGraphAt (F := G) B x) (x : frontier B) :
    outwardNormalPair B hB first x = outwardNormalPair B hB second x :=
  Prod.ext rfl ((first x).outwardNormal_unique (second x) hB)

theorem inwardNormalPair_independent (B : Set E) (hB : IsRegularClosed B)
    (first : (x : frontier B) → C1FrontierGraphAt (F := F) B x)
    (second : (x : frontier B) → C1FrontierGraphAt (F := G) B x) (x : frontier B) :
    inwardNormalPair B hB first x = inwardNormalPair B hB second x :=
  Prod.ext rfl (congrArg Neg.neg ((first x).outwardNormal_unique (second x) hB))

theorem outwardNormalBundle_independent (B : Set E) (hB : IsRegularClosed B)
    (first : (x : frontier B) → C1FrontierGraphAt (F := F) B x)
    (second : (x : frontier B) → C1FrontierGraphAt (F := G) B x) :
    outwardNormalBundle B hB first = outwardNormalBundle B hB second := by
  unfold outwardNormalBundle
  exact congrArg range (funext (outwardNormalPair_independent B hB first second))

theorem inwardNormalBundle_independent (B : Set E) (hB : IsRegularClosed B)
    (first : (x : frontier B) → C1FrontierGraphAt (F := F) B x)
    (second : (x : frontier B) → C1FrontierGraphAt (F := G) B x) :
    inwardNormalBundle B hB first = inwardNormalBundle B hB second := by
  unfold inwardNormalBundle
  exact congrArg range (funext (inwardNormalPair_independent B hB first second))

end BoundedUncertainty
