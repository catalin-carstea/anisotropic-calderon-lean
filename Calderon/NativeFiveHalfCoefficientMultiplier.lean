import Calderon.NativeFiveHalfHarmonicCoherence
import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.NativeCoefficientMultiplierOrderCoherence

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.NativeFiveHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH3FiveHalfValueTrace NativeH2ThreeHalfValueTrace NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] nativeFiveHalfValueTraceL nativeThreeHalfValueTraceL
  coefficientMultiplier NativeFiveHalfHarmonicLift.harmonicLiftCompletion
  NativeHarmonicLiftCompletion.harmonicLiftCompletion

def nativeFiveHalfCoefficientMulL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 4) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (5/2:ℝ) :=
  (nativeFiveHalfValueTraceL hcalc hF hO hD τ0).comp
    ((coefficientMultiplier hcalc 3 F).comp
      (NativeFiveHalfHarmonicLift.harmonicLiftCompletion hF))

lemma sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 4) (G : SmoothCoefficientJets 3)
    (hFG : coefficientValue 4 F = coefficientValue 3 G) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F u) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  change sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
    (nativeFiveHalfValueTraceL hcalc hF hO hD τ0
      (coefficientMultiplier hcalc 3 F (NativeFiveHalfHarmonicLift.harmonicLiftCompletion hF u))) = _
  rw [sphereSobolevInclusionL_nativeFiveHalfValueTraceL,
    lowerOrder_coefficientMultiplier_of_value_eq hcalc 2 F G hFG,
    NativeFiveHalfHarmonicLift.lowerOrder_harmonicLiftCompletion hF hO]
  rfl

lemma norm_nativeFiveHalfCoefficientMulL_le (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 4) :
    ‖nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F‖ ≤
      ‖nativeFiveHalfValueTraceL hcalc hF hO hD τ0‖ *
        ((sobolevMultiplierBound hcalc 3*‖F‖)*‖NativeFiveHalfHarmonicLift.harmonicLiftCompletion hF‖) := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_coefficientMultiplier_le hcalc 3 F) (norm_nonneg _))

end OAI.AnisotropicCalderon.NativeFiveHalfCoefficientMultiplier
