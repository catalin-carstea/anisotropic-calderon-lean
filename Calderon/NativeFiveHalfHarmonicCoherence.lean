import Calderon.NativeFiveHalfHarmonicCompletion
import Calderon.NativeH3FiveHalfValueTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeFiveHalfHarmonicLift
open NativePolynomialBulkMoments NativeHarmonicLiftCompletion
  SphereHarmonic DirichletFamily NativeH2ThreeHalfValueTrace NativeH3FiveHalfValueTrace

lemma sphereSobolevInclusionL_harmonicBoundaryFiniteL (a : HarmonicFiniteCoefficients) :
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (harmonicBoundaryFiniteL a) =
      NativeHarmonicLiftCompletion.harmonicBoundaryFiniteL a := by
  rw [harmonicBoundaryFiniteL_eq_sum,NativeHarmonicLiftCompletion.harmonicBoundaryFiniteL_eq_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact sphereSobolevInclusionL_single (5/2:ℝ) (3/2:ℝ) (by norm_num) k (a k)

lemma lowerOrder_harmonicNativeFiniteL (hF : SphereFischerInner) (a : HarmonicFiniteCoefficients) :
    TauCeti.Wkp.lowerOrder 2 (harmonicNativeFiniteL hF a) =
      NativeHarmonicLiftCompletion.harmonicNativeFiniteL hF a := by
  rw [harmonicNativeFiniteL_eq_polynomial,
    NativeHarmonicLiftCompletion.harmonicNativeFiniteL_eq_polynomial]
  exact lowerOrder_smoothBallSobolev 2 _

lemma lowerOrder_harmonicLiftCompletion (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (u : SphereSobolev (5/2:ℝ)) :
    TauCeti.Wkp.lowerOrder 2 (harmonicLiftCompletion hF u) =
      NativeHarmonicLiftCompletion.harmonicLiftCompletion hF
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  let A : SphereSobolev (5/2:ℝ) →L[ℝ] BallSobolev 2 :=
    (nativeLowerOrderL 2).comp (harmonicLiftCompletion hF)
  let B : SphereSobolev (5/2:ℝ) →L[ℝ] BallSobolev 2 :=
    (NativeHarmonicLiftCompletion.harmonicLiftCompletion hF).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))
  have he : (A : SphereSobolev (5/2:ℝ) → BallSobolev 2) = B := by
    apply denseRange_harmonicBoundaryFiniteL.equalizer A.continuous B.continuous
    funext a
    change nativeLowerOrderL 2 (harmonicLiftCompletion hF (harmonicBoundaryFiniteL a)) =
      NativeHarmonicLiftCompletion.harmonicLiftCompletion hF
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (harmonicBoundaryFiniteL a))
    rw [nativeLowerOrderL_apply,sphereSobolevInclusionL_harmonicBoundaryFiniteL,
      harmonicLiftCompletion_finite hF hO,
      NativeHarmonicLiftCompletion.harmonicLiftCompletion_finite hF hO,
      lowerOrder_harmonicNativeFiniteL]
  exact (nativeLowerOrderL_apply 2 _).symm.trans (congr_fun he u)

lemma nativeFiveHalfValueTraceL_harmonicLiftCompletion (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (u : SphereSobolev (5/2:ℝ)) :
    nativeFiveHalfValueTraceL hcalc hF hO hD τ0 (harmonicLiftCompletion hF u) = u := by
  apply sphereSobolevInclusionL_injective (5/2:ℝ) (3/2:ℝ) (by norm_num)
  rw [sphereSobolevInclusionL_nativeFiveHalfValueTraceL,
    lowerOrder_harmonicLiftCompletion hF hO,
    nativeThreeHalfValueTraceL_harmonicLiftCompletion]

end OAI.AnisotropicCalderon.NativeFiveHalfHarmonicLift
