import Calderon.ActualReferenceTwoAngleNormalEndpointInverseFamilies
import Calderon.ActualReferenceNormalHalfInverseDualAdjunction
import Calderon.ActualReferenceTwoAngleNormalDriftEndpointFamilies
import Calderon.NativeHarmonicHalfCoarseDualPairing

/-! SAME ordinary normal reciprocal and actual beta. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)

lemma referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible_of_referenceData (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    (referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).IsInvertible := by
  exact referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t.1 t.2.1 t.2.2
      (referenceNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t.2.2)

lemma sphereSobolevDualPairing_referenceTwoAngleNormalBoundaryMultiplier_inverse
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (v : SphereSobolev (1/2:ℝ)) (y : SphereSobolev (-(1/2:ℝ))) :
    sphereSobolevDualPairing (1/2:ℝ) v
      ((referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).inverse y) =
    sphereSobolevDualPairing (1/2:ℝ)
      ((referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).inverse v) y := by
  let A := referenceTwoAngleNormalHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  let BN := referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  have hA : A.IsInvertible := referenceTwoAngleNormalHalfMultiplierFamily_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  have hB : BN.IsInvertible := referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t
  have hPair : ⟪A.inverse v,BN (BN.inverse y)⟫_ℝ = ⟪A (A.inverse v),BN.inverse y⟫_ℝ :=
    ContinuousLinearMap.adjoint_inner_right A (A.inverse v) (BN.inverse y)
  have hLeft : ⟪A.inverse v,BN (BN.inverse y)⟫_ℝ = ⟪A.inverse v,y⟫_ℝ :=
    congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => ⟪A.inverse v,z⟫_ℝ) (hB.self_apply_inverse y)
  have hRight : ⟪A (A.inverse v),BN.inverse y⟫_ℝ = ⟪v,BN.inverse y⟫_ℝ :=
    congrArg (fun z : SphereSobolev (1/2:ℝ) => ⟪z,BN.inverse y⟫_ℝ) (hA.self_apply_inverse v)
  exact (hLeft.symm.trans (hPair.trans hRight)).symm


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeOrderOneCoefficientMultiplier
  NativeHarmonicH1LiftCompletion NativeHarmonicHalfCoarseDualPairing
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma sphereSobolevDualPairing_referenceTwoAngleNormalDriftHalfMultiplier
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA kA lA : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (f v : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) f
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceTwoAngleNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t v)) =
    ⟪sphereContinuousScalarMulL (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
        (fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x))
        (SpatialJetFields.contDiff_spatial_slice _
          (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 t)))
      (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF v)),
      τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF f)⟫_ℝ := by
  let F3 := referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 3 t
  let F2 := referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 t
  let M := referenceTwoAngleNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA hcalc hF hO hD τ0 t
  let Z := sphereSobolevZeroEquiv hO hD
  let I := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let K := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let beta := fun x => referenceTwoAngleDriftFamily g L Φ H w iA jA kA lA (t,x)
  have hbeta : ContDiff ℝ ∞ beta :=
    SpatialJetFields.contDiff_spatial_slice _
      (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData iA jA kA lA).1 t
  let CN := sphereContinuousScalarMulL (nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData beta hbeta))
  have hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2 := by
    funext x
    exact (coefficientValue_referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 3 t x).trans
      (coefficientValue_referenceTwoAngleNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA kA lA 2 t x).symm
  have hBase := sphereSobolevInclusionL_nativeHalfCoefficientMulL_sameValue hcalc hF hO hD τ0 F3 F2 hCoeff v
  have hSphere := smoothSphereValue_referenceTwoAngleNormalDriftJetsFamily_eq_native g L y0 Φ B ε C ρ H a w hData iA jA kA lA t
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
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleNormalDriftHalfMultiplier

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalBoundaryMultiplierFamily_isInvertible_of_referenceData
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceTwoAngleNormalBoundaryMultiplier_inverse
