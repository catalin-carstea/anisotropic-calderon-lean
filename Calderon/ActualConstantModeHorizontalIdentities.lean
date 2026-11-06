import Calderon.ActualSphereSobolevConstantOne
import Calderon.ActualWeightedHorizontalActions
import Calderon.SphereSobolevSingleRotationAngleDerivative
import Calderon.SmoothSphereRotationProjection
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SmoothSphereRotationProjection

theorem sphereSobolevRotationL_constantOne (s : ℝ) (i j : Fin 3) :
    sphereSobolevRotationL s i j (sphereSobolevConstantOne s) = 0 := by
  unfold sphereSobolevConstantOne
  rw [sphereSobolevRotationL_single,harmonicSphereRotation_degree_zero]
  simp only [ContinuousLinearMap.zero_apply,map_zero]

theorem sphereSobolevShiftedDegreeL_constantOne (s : ℝ) :
    sphereSobolevShiftedDegreeL s (sphereSobolevConstantOne s) = 0 := by
  unfold sphereSobolevConstantOne
  rw [sphereSobolevShiftedDegreeL_single]
  simp only [Nat.cast_zero,zero_smul]

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
attribute [local irreducible] sphereSobolevConstantOne sphereSobolevInclusionL
  sphereSobolevRotationL sphereSobolevShiftedDegreeL referenceMetricGramFrame
  referenceFrameConnectionCoefficient referenceRadiusHorizontalLogDerivative

theorem referenceHighHorizontalAction_constantOne
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    referenceHighHorizontalAction g L q (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y i = 0 := by
  simp only [referenceHighHorizontalAction,referenceHighHorizontalAngularL,
    fderiv_const_apply,ContinuousLinearMap.zero_apply,map_zero,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    sphereSobolevRotationL_constantOne,smul_zero,Finset.sum_const_zero,add_zero]

theorem referenceLowerHorizontalAction_constantOne
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    referenceLowerHorizontalAction g L q (fun _ => sphereSobolevConstantOne (1/2:ℝ)) y i = 0 := by
  simp only [referenceLowerHorizontalAction,referenceLowerHorizontalAngularL,
    fderiv_const_apply,ContinuousLinearMap.zero_apply,map_zero,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    sphereSobolevRotationL_constantOne,smul_zero,Finset.sum_const_zero,add_zero]

theorem referenceHighWeightedHorizontalAction_constantOne
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    referenceHighWeightedHorizontalAction g L q R
      (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y i = 0 := by
  simp only [referenceHighWeightedHorizontalAction,referenceHighHorizontalAction_constantOne,
    sphereSobolevShiftedDegreeL_constantOne,smul_zero,add_zero]

theorem referenceLowerWeightedHorizontalAction_constantOne
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    referenceLowerWeightedHorizontalAction g L q R
      (fun _ => sphereSobolevConstantOne (1/2:ℝ)) y i = 0 := by
  simp only [referenceLowerWeightedHorizontalAction,referenceLowerHorizontalAction_constantOne,
    sphereSobolevShiftedDegreeL_constantOne,smul_zero,add_zero]

theorem referenceLowerWeightedHorizontalAction_zero
    (g : MatrixField) (L q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    referenceLowerWeightedHorizontalAction g L q R
      (fun _ => (0 : SphereSobolev (1/2:ℝ))) y i = 0 := by
  simp only [referenceLowerWeightedHorizontalAction,referenceLowerHorizontalAction,
    referenceLowerHorizontalAngularL,fderiv_const_apply,ContinuousLinearMap.zero_apply,
    map_zero,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    smul_zero,Finset.sum_const_zero,add_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
