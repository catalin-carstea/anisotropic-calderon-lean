import Calderon.ActualNativeMovingRadiusTrace
import Calderon.NativeLinearCoordinateMultiplierIdentification
import Calderon.NativeThreeHalfCoefficientMultiplier
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual Pi scalar and coordinate identifications; complete upfront P1/P2 in
Opus v006 MATHEMATICS.md, with Root-authored proofs. No radius at zero is used. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame

lemma radius_mul_referenceRadiusHorizontalLogDerivative
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hpos : 0 < R y) :
    R y * referenceRadiusHorizontalLogDerivative g L q R y i =
      fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) := by
  unfold referenceRadiusHorizontalLogDerivative
  rw [fderiv.log hR hpos.ne']
  rw [ContinuousLinearMap.smul_apply,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
attribute [local irreducible] nativeThreeHalfCoefficientMulL sphereSobolevInclusionL
  sphereSobolevLinearCoordinateMulL

lemma nativeThreeHalfCoefficientMulL_eq_linearCoordinateMulL_of_sphereValue
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 3) (d : R3)
    (hSphere : smoothSphereValue (nativeH2CoefficientSmoothData F) =
      ∑ i : Fin 3, (d i) • sphereCoordinate i) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) d := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  have hScalar : sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F)) =
      sphereLinearCoordinateMulL d :=
    (congrArg (fun m => sphereContinuousScalarMulL m) hSphere).trans
      (sphereLinearCoordinateMulL_eq_linear_scalarMulL d).symm
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  have hNativeGraph : I (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F u) =
      Z (sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F)) (Z.symm (I u))) :=
    sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 F u
  have hLinearGraph : I (sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) d u) =
      Z (sphereLinearCoordinateMulL d (Z.symm (I u))) :=
    sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv hF hO hD (3/2 : ℝ) (by norm_num)
      d u (Z.symm (I u)) (Z.apply_symm_apply (I u)).symm
  exact hNativeGraph.trans
    ((congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm (I u)))) hScalar).trans hLinearGraph.symm)

end OAI.AnisotropicCalderon.SphereHarmonic
