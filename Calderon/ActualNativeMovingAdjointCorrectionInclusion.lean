import Calderon.ActualNativeMovingAdjointFiniteJ
import Calderon.ActualFirstCorrectionSobolevFamilies
import Calderon.SphereSobolevCoordinateInclusion

/-! SAME actual correction at all finite placements, multiplier remains on right. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame

attribute [local irreducible] referenceNativeMovingAdjointParametricCorrection
  sphereSobolevRadialDriftAdjointL sphereSobolevLinearCoordinateMulL sphereSobolevInclusionL

lemma referenceNativeMovingAdjointParametricCorrection_inclusion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L s t : ℝ) (hts : t ≤ s)
    (z : (ℝ × R3) × (R3 →L[ℝ] ℝ)) (i : Fin 3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts
      (referenceNativeMovingAdjointParametricCorrection hF hO hD g L s z i u) =
      referenceNativeMovingAdjointParametricCorrection hF hO hD g L t z i
        (sphereSobolevInclusionL s t hts u) := by
  let d := referenceCenterDrift g L z.1.1 z.1.2
  let c := z.2 (conformalReferenceGramFrameOperatorJoint g L z.1 (coordinateVector i))
  let I := sphereSobolevInclusionL s t hts
  let Ds := sphereSobolevRadialDriftAdjointL hF hO hD s d
  let Dt := sphereSobolevRadialDriftAdjointL hF hO hD t d
  let Ms := sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1)
  let Mt := sphereSobolevLinearCoordinateMulL hF hO hD t (EuclideanSpace.single i 1)
  have hD1 : I (Ds (Ms u)) = Dt (I (Ms u)) :=
    sphereSobolevInclusionL_radialDriftAdjoint hF hO hD s t hts d (Ms u)
  have hM : I (Ms u) = Mt (I u) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD s t hts (EuclideanSpace.single i 1) u
  have hD2 : I (Ds u) = Dt (I u) :=
    sphereSobolevInclusionL_radialDriftAdjoint hF hO hD s t hts d u
  have hValue := congrArg₂ (fun a b : SphereSobolev t => a+b)
    (hD1.trans (congrArg Dt hM)) (congrArg (fun v : SphereSobolev t => c • v) hD2)
  simpa (config := { instances := true }) only
    [referenceNativeMovingAdjointParametricCorrection,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,map_add,map_smul,I,Ds,Dt,Ms,Mt,d,c]
    using hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeMovingAdjointParametricCorrection_inclusion
