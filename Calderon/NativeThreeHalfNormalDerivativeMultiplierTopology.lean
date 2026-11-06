import Calderon.NativeThreeHalfNormalDerivativeMultiplier
import Calderon.NativeRepackedCoefficientMultiplierTopology
import Calderon.NativeSmoothMultiplierCommonSupportJets

/-! Joint topology of the high normal term. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeThreeHalfCoefficientMultiplier
variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]

lemma contDiff_nativeThreeHalfNormalDerivativeMulL_commonSupport
    (q : T × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → q (t,x)=0)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun t => nativeThreeHalfNormalDerivativeMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 q hq K hK hz t)) := by
  have hTerm (i : Fin 3) : ContDiff ℝ ∞ (fun t => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (coefficientRepackedJets 2 3
        (smoothMultiplierDerivativeJets (commonSupportCoefficientFamily 3 q hq K hK hz t) i))) := by
    apply contDiff_repackedNativeThreeHalfCoefficientMulL_of_value_graph hcalc hF hO hD τ0 2
      (smoothMultiplierSpatialDerivative q i) (contDiff_smoothMultiplierSpatialDerivative q hq i)
      K hK (smoothMultiplierSpatialDerivative_zero_outside q hq K hK hz i)
    intro t
    rw [smoothMultiplierDerivativeJets_commonSupport]
    funext x
    exact coefficientValue_commonSupportCoefficientFamily 2
      (smoothMultiplierSpatialDerivative q i) (contDiff_smoothMultiplierSpatialDerivative q hq i)
      K hK (smoothMultiplierSpatialDerivative_zero_outside q hq K hK hz i) t x
  unfold nativeThreeHalfNormalDerivativeMulL
  exact ContDiff.sum (fun i _ => contDiff_const.clm_comp (hTerm i))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeThreeHalfNormalDerivativeMulL_commonSupport

