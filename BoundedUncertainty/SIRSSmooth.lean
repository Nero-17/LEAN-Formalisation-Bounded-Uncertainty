import BoundedUncertainty.SIRSSystem
import BoundedUncertainty.SmoothBoundaryInverse

/-! The same concrete SIRS system carries fixed C-infinity data and the full smooth
boundary-map theorem, rather than merely an unrelated family of finite-order systems. -/
namespace BoundedUncertainty
open Set Topology
open scoped ContDiff

theorem sirsSystem_map_smooth (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) :
    HasSmoothLocalExtensionOn (sirsSystem r s hr hs κ hκ hthreshold).domain
      (sirsSystem r s hr hs κ hκ hthreshold).map :=
  hasSmoothLocalExtensionOn_of_contDiff _ _ (contDiff_sirsMap (1 / 10) 1 3 ∞)

theorem sirsSystem_radius_smooth (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) :
    HasSmoothLocalExtensionOn (sirsSystem r s hr hs κ hκ hthreshold).domain
      (sirsSystem r s hr hs κ hκ hthreshold).radius :=
  hasSmoothLocalExtensionOn_of_contDiff _ _ (contDiff_sirsRadius κ ∞)

theorem sirsSystem_inverse_smooth (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) :
    HasSmoothLocalExtensionOn ((sirsSystem r s hr hs κ hκ hthreshold).map ''
      (sirsSystem r s hr hs κ hκ hthreshold).domain)
      (sirsSystem r s hr hs κ hκ hthreshold).diffeomorphism.inverse :=
  sirsAmbientDiffeomorphism_inverse_smooth s

theorem sirsSystem_boundary_smooth_homeomorphism (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (κ : ℝ) (hκ : 0 ≤ κ) (hthreshold : κ < 20 * Real.sqrt 2) :
    IsEmbedding (sirsSystem r s hr hs κ hκ hthreshold).boundaryFormula ∧
      HasSmoothLocalExtensionOn (sirsSimplex ×ˢ {n : EuclideanSpace ℝ (Fin 2) | ‖n‖ = 1})
        (sirsSystem r s hr hs κ hκ hthreshold).boundaryFormulaOnAmbient ∧
      HasSmoothLocalExtensionOn (range (sirsSystem r s hr hs κ hκ hthreshold).boundaryFormula)
        ((sirsSystem r s hr hs κ hκ hthreshold).boundaryInverseOnAmbient
          (sirsSystem_isContraction r s hr hs κ hκ hthreshold)) :=
  (sirsSystem r s hr hs κ hκ hthreshold).boundaryFormula_smooth_homeomorphism
    (sirsSystem_isContraction r s hr hs κ hκ hthreshold)
    (sirsSystem_map_smooth r s hr hs κ hκ hthreshold)
    (sirsSystem_radius_smooth r s hr hs κ hκ hthreshold)
    (sirsSystem_inverse_smooth r s hr hs κ hκ hthreshold)

end BoundedUncertainty
