import Calderon.ActualReferenceRotationCoefficientJets
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.NativeSupportedAdjointWeakSolution

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (iA jA : Fin 3)

def referenceRotationNormalDriftFunction (q : (ℝ × (ℝ × (R3 × ℝ))) × R3) : ℝ :=
  ∑ i : Fin 3, q.2 i * coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) q i

include hData
lemma contDiff_referenceRotationNormalDriftFunction :
    ContDiff ℝ ∞ (referenceRotationNormalDriftFunction g L Φ H w iA jA) := by
  apply ContDiff.sum
  intro i hi
  exact ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1)

lemma referenceRotationNormalDriftFunction_zero_outside
    (t : ℝ × (ℝ × (R3 × ℝ))) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    referenceRotationNormalDriftFunction g L Φ H w iA jA (t,x) = 0 := by
  unfold referenceRotationNormalDriftFunction
  rw [(referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).2 t x hx]
  simp

def referenceRotationNormalDriftJetsFamily (n : ℕ) (t : ℝ × (ℝ × (R3 × ℝ))) : SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceRotationNormalDriftFunction g L Φ H w iA jA)
    (contDiff_referenceRotationNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA) t

lemma coefficientValue_referenceRotationNormalDriftJetsFamily (n : ℕ) (t : ℝ × (ℝ × (R3 × ℝ))) (x : R3) :
    coefficientValue n (referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA n t) x =
      referenceRotationNormalDriftFunction g L Φ H w iA jA (t,x) :=
  coefficientValue_commonSupportCoefficientFamily n (referenceRotationNormalDriftFunction g L Φ H w iA jA)
    (contDiff_referenceRotationNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA) t x

lemma smoothSphereValue_referenceRotationNormalDriftJetsFamily_eq_native (t : ℝ × (ℝ × (R3 × ℝ))) :
    smoothSphereValue (nativeH2CoefficientSmoothData
      (referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 3 t)) =
    nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
      (fun x => coordinateRotationDriftFamily iA jA (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData iA jA).1 t)) := by
  ext x
  have hv := coefficientValue_referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 3 t (x : R3)
  change coefficientValue 3 (referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 3 t) (x : R3) = _
  rw [hv]
  simp only [referenceRotationNormalDriftFunction,nativeNormalDriftCoefficient,
    ContinuousMap.sum_apply,ContinuousMap.mul_apply,sphereCoordinate,smoothSphereValue,
    ContinuousMap.coe_mk,nativeSupportedDriftSmoothData]
  rfl

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceRotationNormalDriftThreeHalfMultiplierFamily (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 3 t)

def referenceRotationNormalDriftHalfMultiplierFamily (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceRotationNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 2 t)

lemma contDiff_referenceRotationNormalDriftThreeHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceRotationNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceRotationNormalDriftFunction g L Φ H w iA jA)
    (contDiff_referenceRotationNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA)

lemma contDiff_referenceRotationNormalDriftHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceRotationNormalDriftFunction g L Φ H w iA jA)
    (contDiff_referenceRotationNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA)

lemma referenceRotationNormalDriftMultiplier_high_half_compatibility (t : ℝ × (ℝ × (R3 × ℝ))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceRotationNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t) =
    (referenceRotationNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 _ _
    (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
      (referenceRotationNormalDriftFunction g L Φ H w iA jA)
      (contDiff_referenceRotationNormalDriftFunction g L y0 Φ B ε C ρ H a w hData iA jA)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceRotationNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData iA jA) t)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalDriftFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalDriftFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalDriftFunction_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceRotationNormalDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSphereValue_referenceRotationNormalDriftJetsFamily_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalDriftThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalDriftHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalDriftThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNormalDriftHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalDriftMultiplier_high_half_compatibility
