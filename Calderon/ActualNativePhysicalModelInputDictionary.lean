import Calderon.ActualFiniteCoreSobolevLift
import Calderon.ActualHorizontalSobolevConnection
import Calderon.ActualFiniteHarmonicModelReference
import Calderon.ActualNativeMovingRadiusTrace
import Calderon.SphereSobolevShiftedPhysicalDegree

/-! Upfront: actual-physical-P-local-allocation-author-oct16-v001/
EXPANSION-model-input-dictionary-v003.md. SAME physical finite input, degree k. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualFiniteHarmonicAmbient
  ConnectionError NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection
  AmbientReferenceRaising RadiusProfile ConformalDepth SmoothSphereRotationProjection

attribute [local irreducible] finiteCoreSobolevLift sphereSobolevInclusionL
  sphereSobolevRotationL sphereSobolevShiftedDegreeL referenceHighHorizontalAngularL
  referenceHighHorizontalAction coreReferenceInput coreReferenceHorizontal
  referenceRadiusHorizontalLogDerivative

lemma referenceHighWeightedHorizontalAction_finiteCoreSobolevLift
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q δ A : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hA : 0 < A)
    (F : smoothCompactFiniteSphereCore hO hD) (y : R3) (i : Fin 3) :
    referenceHighHorizontalAction g L q (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) y i +
      referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i •
        sphereSobolevShiftedDegreeL (3/2 : ℝ)
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) F y) =
      finiteCoreSobolevLift hO hD (1/2 : ℝ)
        (coreReferenceInput hO hD g hg L q δ A p i hδ hA F) y := by
  let U := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let X := referenceMetricGramFrame g L (q,y) i
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius δ A p L) y i
  let Gamma := fun a b : Fin 3 => referenceFrameConnectionCoefficient g L q y X a b
  have hFrame : conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i) = X :=
    (congrArg (fun T : R3 →L[ℝ] R3 => T (coordinateVector i))
      (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,y))).trans
        ((frameOperator_coordinateVector _ i).trans
          (conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q y i))
  have hScalar : f = referenceFrameDerivative g L q i
      (fun x => Real.log (referenceRadius δ A p L x)) y := by
    dsimp only [f]
    unfold referenceRadiusHorizontalLogDerivative referenceFrameDerivative
    exact congrArg (fderiv ℝ (fun x => Real.log (referenceRadius δ A p L x)) y) hFrame
  have hUSmooth : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hUDiff := hUSmooth.differentiable (by simp) y
  have hFDiff := F.property.1.differentiable (by simp) y
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  let c := sphereHarmonicCoordinate hO hD k
  let v := c (F.val y)
  have hFunction : (fun x : R3 => sphereSobolevCoefficientL (3/2 : ℝ) k (U x)) =
      (fun x : R3 => c (F.val x)) :=
    funext (fun x => sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F x k)
  have hNativeDerivative := congrArg
    (fun T : R3 →L[ℝ] harmonicSphereSubspace k => T X)
    (((sphereSobolevCoefficientL (3/2 : ℝ) k).hasFDerivAt.comp y hUDiff.hasFDerivAt).fderiv)
  have hFunctionDerivative := congrArg
    (fun V : R3 → harmonicSphereSubspace k => fderiv ℝ V y X) hFunction
  have hCoreDerivative := congrArg
    (fun T : R3 →L[ℝ] harmonicSphereSubspace k => T X)
    (fderiv_sphereHarmonicCoordinate hO hD k F.val y hFDiff)
  have hBase : sphereSobolevCoefficientL (3/2 : ℝ) k (fderiv ℝ U y X) =
      c (fderiv ℝ F.val y X) := by
    simpa (config := { instances := true }) only [ContinuousLinearMap.comp_apply,c]
      using hNativeDerivative.symm.trans (hFunctionDerivative.trans hCoreDerivative)
  have hUValue : sphereSobolevCoefficientL (3/2 : ℝ) k (U y) = v :=
    sphereSobolevCoefficientL_finiteCoreSobolevLift hO hD (3/2 : ℝ) F y k
  have hRot (a b : Fin 3) : sphereSobolevCoefficientL (1/2 : ℝ) k
      (sphereSobolevRotationL (3/2 : ℝ) a b (U y)) = harmonicSphereRotation k a b v := by
    have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
      (sphereSobolevRotationL (3/2 : ℝ) a b (U y)))
      (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
    exact hIndex.symm.trans
      ((sphereSobolevCoefficientL_rotation (3/2 : ℝ) a b k (U y)).trans
        (congrArg (harmonicSphereRotation k a b) hUValue))
  have hDegree : sphereSobolevCoefficientL (1/2 : ℝ) k
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U y)) = (k : ℝ) • v := by
    have hIndex := congrArg (fun t : ℝ => sphereSobolevCoefficientL t k
      (sphereSobolevShiftedDegreeL (3/2 : ℝ) (U y)))
      (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
    exact hIndex.symm.trans
      ((sphereSobolevCoefficientL_shiftedDegree (3/2 : ℝ) k (U y)).trans
        (congrArg (fun w : harmonicSphereSubspace k => (k : ℝ) • w) hUValue))
  have hHorizontal : sphereSobolevCoefficientL (1/2 : ℝ) k
      (referenceHighHorizontalAction g L q U y i) =
      c (fderiv ℝ F.val y X) + (1/2 : ℝ) •
        ∑ a : Fin 3, ∑ b : Fin 3, Gamma a b • harmonicSphereRotation k a b v := by
    simp (config := { instances := true }) only
      [referenceHighHorizontalAction,referenceHighHorizontalAngularL,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
        map_add,map_smul,map_sum,sphereSobolevCoefficientL_inclusion,hBase,hRot,Gamma,X]
  have hCoreHorizontal : c ((coreReferenceHorizontal hO hD g hg L q i F).val y) =
      c (fderiv ℝ F.val y X) + (1/2 : ℝ) •
        ∑ a : Fin 3, ∑ b : Fin 3, Gamma a b • harmonicSphereRotation k a b v := by
    have h := congrArg c (coreReferenceHorizontal_apply hO hD g hg L q i F y)
    simpa (config := { instances := true }) only
      [coreFrameHorizontalAction,map_add,map_smul,map_sum,coreRotation,
        coreBlockOperator_coordinate,c,X,Gamma,v] using h
  have hCoreDegree : c ((coreDegree hO hD F).val y) = (k : ℝ) • v :=
    coreWeightOperator_graph hO hD (fun n => (n : ℝ)) F y k
  have hInput : c ((coreReferenceInput hO hD g hg L q δ A p i hδ hA F).val y) =
      c ((coreReferenceHorizontal hO hD g hg L q i F).val y) +
        f • c ((coreDegree hO hD F).val y) := by
    simp (config := { instances := true }) only
      [coreReferenceInput,LinearMap.add_apply,Module.End.mul_apply,coreScalar,
        LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_add,
        Pi.add_apply,map_add,map_smul,← hScalar,c]
  have hBoth := congrArg₂ (fun a b : harmonicSphereSubspace k => a+f • b) hHorizontal hDegree
  have hCoreBoth := congrArg₂ (fun a b : harmonicSphereSubspace k => a+f • b)
    hCoreHorizontal hCoreDegree
  simpa (config := { instances := true }) only
    [map_add,map_smul,sphereSobolevCoefficientL_finiteCoreSobolevLift,U,f,c]
    using hBoth.trans (hCoreBoth.symm.trans hInput.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighWeightedHorizontalAction_finiteCoreSobolevLift
