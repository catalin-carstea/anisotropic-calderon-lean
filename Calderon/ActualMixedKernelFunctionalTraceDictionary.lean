import Calderon.ActualMixedKernelScalarTransfer
import Calderon.NativeHighDensityTracePairingDictionary

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace ReferenceWeightedApproximation ConformalDepth ConnectionError ExteriorSource

theorem nativeMixedKernelDensityFunctional_eq_native_dualTracePairing
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam delta Rstar : ℝ) (p : ℕ) (Psi : R3 → SphereSobolev (3/2 : ℝ))
    (u : SmoothData) (y : R3) :
    nativeMixedKernelDensityFunctional hO hD τ0 S L P lam delta Rstar p Psi u y =
      sphereSobolevDualPairing (-(1/2 : ℝ))
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (Psi y)))
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2
            (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
              P.native_data.1.1.1 lam y (referenceRadius delta Rstar p L y) u)))) := by
  exact (nativeThreeHalfTrace_dualPairing_eq_L2_valueTrace
    hcalc hF hO hD τ0 (Psi y)
    (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B
      P.native_data.1.1.1 lam y (referenceRadius delta Rstar p L y) u)).symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
