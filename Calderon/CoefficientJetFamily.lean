import Calderon.CoefficientJetSpace
import Calderon.SpatialJetFields

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

def commonSupportCoefficientFamily (r : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) : SmoothCoefficientJets r :=
  compactCoefficient r (fun x => g (t,x))
    (SpatialJetFields.contDiff_spatial_slice g hg t)
    (SpatialJetFields.hasCompactSupport_spatial_slice g K hK hz t)

theorem coefficientValue_commonSupportCoefficientFamily (r : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) (x : R3) :
    coefficientValue r (commonSupportCoefficientFamily r g hg K hK hz t) x = g (t,x) :=
  congrFun (coefficientValue_compactCoefficient r _ _ _) x

theorem commonSupportCoefficientFamily_jet (r : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) (j : Fin (r + 1)) (x : R3) :
    (commonSupportCoefficientFamily r g hg K hK hz t).1 j x =
      iteratedFDeriv ℝ j.val (fun y => g (t,y)) x := rfl

theorem contDiff_commonSupportCoefficientFamily_val (r : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (fun t => (commonSupportCoefficientFamily r g hg K hK hz t).1) := by
  apply contDiff_pi.mpr
  intro j
  convert SpatialJetFields.contDiff_infty_spatialJetSlice j.val g hg K hK hz using 1
  funext t
  apply BoundedContinuousFunction.ext
  intro x
  exact (SpatialJetFields.spatialJetField_eq_iteratedFDeriv j.val g hg t x).symm

theorem continuous_commonSupportCoefficientFamily (r : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    Continuous (commonSupportCoefficientFamily r g hg K hK hz) :=
  continuous_induced_rng.mpr
    (contDiff_commonSupportCoefficientFamily_val r g hg K hK hz).continuous

end OAI.AnisotropicCalderon.DirichletFamily
