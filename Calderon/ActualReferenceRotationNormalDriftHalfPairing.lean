import Calderon.ActualReferenceRotationNormalDriftEndpointFamilies
import Calderon.NativeHarmonicHalfCoarseDualPairing
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeOrderOneCoefficientMultiplier
  NativeHarmonicH1LiftCompletion NativeHarmonicHalfCoarseDualPairing
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma sphereSobolevDualPairing_referenceRotationNormalDriftHalfMultiplier
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (f v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) f
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t v)) =
    ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
        (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1 t)))
      (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF v)),
      τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)⟫_ℝ := by
  let F3 := referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 3 t
  let F2 := referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 2 t
  let M := referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t
  let Z := sphereSobolevZeroEquiv hO hD
  let I := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let K := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let beta := fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  have hbeta : ContDiff ℝ ∞ beta :=
    SpatialJetFields.contDiff_spatial_slice _
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1 t
  let CN := sphereContinuousScalarMulL (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
  have hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2 := by
    funext x
    exact (coefficientValue_referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 3 t x).trans
      (coefficientValue_referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 2 t x).symm
  have hBase := sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue hcalc hF hO hD τ0 F3 F2 hCoeff v
  have hSphere := smoothSphereValue_referenceRotationNormalDriftJetsFamily_eq_native g L y0 Φ B ε C ρ H a w hData iA jA t
  have hGraph : I (M v) = Z (CN (Z.symm (I v))) :=
    hBase.trans (congrArg (fun m : C(UnitSphere,ℝ) => Z
      (sphereContinuousScalarMulL m (Z.symm (I v)))) hSphere)
  have hTrace : Z.symm (I v) = τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF v) :=
    (congrArg Z.symm (sphereSobolevZeroEquiv_valueTrace_harmonicFirstOrderLift hF hO hD τ0 v)).symm.trans
      (Z.symm_apply_apply (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF v)))
  have hTrans : J (I (M v)) = K (M v) :=
    congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T (M v))
      (sphereSobolevInclusionL_trans (1/2:ℝ) 0 (-(1/2:ℝ)) (by norm_num) (by norm_num))
  have hCoarse : K (M v) = J (Z (CN (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF v)))) :=
    hTrans.symm.trans ((congrArg J hGraph).trans
      (congrArg (fun z : SphereL2 => J (Z (CN z))) hTrace))
  exact (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) f z) hCoarse).trans
    (sphereSobolevDualPairing_coarse_eq_halfLift_trace hF hO hD τ0 f
      (CN (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF v))))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceRotationNormalDriftHalfMultiplier
