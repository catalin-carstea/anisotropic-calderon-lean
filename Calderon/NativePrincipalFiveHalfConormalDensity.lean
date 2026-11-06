import Calderon.NativeH4FiveHalfCoefficientConormalTrace
import Calderon.NativeH4H3PrincipalProjectionCoherence
import Calderon.NativePrincipalHarmonicConormalDensity

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH4FiveHalfCoefficientConormalTrace
  NativeH3CoefficientConormalTrace NativePolynomialBulkMoments

/-- Five-half density from the same order-four principal harmonic correction. -/
def nativePrincipalFiveHalfConormalDensity
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (r : ℝ) (F : SmoothCoefficientMatrix 4) (E : BallSobolev 4) :
    SphereSobolev (5/2 : ℝ) :=
  (r * sphereSurfaceMass) • nativeFiveHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F
    (strongHarmonicProjectionL 2 (ordinaryPrincipalL hcalc 2 F) E - E)

attribute [local irreducible] nativeFiveHalfCoefficientConormalTraceL
  nativeThreeHalfCoefficientConormalTraceL strongHarmonicProjectionL sphereSobolevInclusionL

/-- Exact inclusion into the already constructed H3/2 density. -/
theorem sphereSobolevInclusionL_nativePrincipalFiveHalfConormalDensity
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (r : ℝ)
    (F : SmoothCoefficientMatrix 4) (G : SmoothCoefficientMatrix 3)
    (hFG : ∀ i j, coefficientValue 4 (F i j) = coefficientValue 3 (G i j))
    (hi4 : ((ordinaryPrincipalL hcalc 2 F).comp
      (strongDirichletSubmodule 2).toSubmodule.subtypeL).IsInvertible)
    (hi3 : ((ordinaryPrincipalL hcalc 1 G).comp
      (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible)
    (E : BallSobolev 4) :
    sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
      (nativePrincipalFiveHalfConormalDensity hcalc hF hO hD τ0 r F E) =
    nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 r G
      (TauCeti.Wkp.lowerOrder 3 E) := by
  rw [nativePrincipalFiveHalfConormalDensity,map_smul]
  rw [sphereSobolevInclusionL_nativeFiveHalfCoefficientConormalTraceL
    hcalc hF hO hD τ0 F G hFG]
  have hLowerSub (u v : BallSobolev 4) :
      TauCeti.Wkp.lowerOrder 3 (u-v) =
        TauCeti.Wkp.lowerOrder 3 u - TauCeti.Wkp.lowerOrder 3 v := by
    change TauCeti.Wkp.lowerOrderL 3 (u-v) = _
    exact map_sub _ _ _
  rw [hLowerSub, lowerOrder_strongHarmonicProjectionL_four_three hcalc F G hFG hi4 hi3 E]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
