import Calderon.NativeFiveHalfCoefficientMultiplierInverse
import Calderon.NativeOrderOneCoefficientMultiplierTopology

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.NativeFiveHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeOrderOneCoefficientMultiplier NativeFiveHalfCoefficientMultiplierInverse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma contDiff_nativeFiveHalfCoefficientMulL_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (phi : E × R3 → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → phi (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : E => nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 4 phi hphi K hK hz p)) := by
  unfold nativeFiveHalfCoefficientMulL
  exact contDiff_const.clm_comp
    ((contDiff_commonSupport_actual_coefficientMultiplier hcalc 3 phi hphi K hK hz).clm_comp contDiff_const)

lemma nativeFiveHalfCoefficientMulL_commonSupport_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (phi : E × R3 → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → phi (p,x) = 0)
    (hpos : ∀ p : E, ∀ x : UnitSphere, 0 < phi (p,x.1)) (p : E) :
    (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 4 phi hphi K hK hz p)).IsInvertible := by
  apply nativeFiveHalfCoefficientMulL_isInvertible_of_pos
  intro x
  rw [coefficientValue_commonSupportCoefficientFamily]
  exact hpos p x

lemma contDiff_nativeFiveHalfCoefficientMulL_commonSupport_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (phi : E × R3 → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → phi (p,x) = 0)
    (hpos : ∀ p : E, ∀ x : UnitSphere, 0 < phi (p,x.1)) :
    ContDiff ℝ ∞ (fun p : E =>
      (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 4 phi hphi K hK hz p)).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (nativeFiveHalfCoefficientMulL_commonSupport_isInvertible
    hcalc hF hO hD τ0 phi hphi K hK hz hpos p).contDiffAt_map_inverse.comp p
      (contDiff_nativeFiveHalfCoefficientMulL_commonSupport
        hcalc hF hO hD τ0 phi hphi K hK hz).contDiffAt

end OAI.AnisotropicCalderon.NativeFiveHalfCoefficientMultiplier
