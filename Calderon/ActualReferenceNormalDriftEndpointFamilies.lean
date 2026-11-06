import Calderon.ActualReferenceWeakEnergyConstruction
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
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceNormalDriftFunction (q : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  ∑ i : Fin 3, q.2 i * conformalReferenceWeightedFramedDrift g L Φ H w q i

include hData
lemma contDiff_referenceNormalDriftFunction :
    ContDiff ℝ ∞ (referenceNormalDriftFunction g L Φ H w) := by
  apply ContDiff.sum
  intro i hi
  exact ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
    ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
      (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1)

lemma referenceNormalDriftFunction_zero_outside
    (p : ℝ × (R3 × ℝ)) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    referenceNormalDriftFunction g L Φ H w (p,x) = 0 := by
  unfold referenceNormalDriftFunction
  rw [(jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p x hx]
  simp

def referenceNormalDriftJetsFamily (n : ℕ) (p : ℝ × (R3 × ℝ)) : SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (referenceNormalDriftFunction g L Φ H w)
    (contDiff_referenceNormalDriftFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p

lemma coefficientValue_referenceNormalDriftJetsFamily (n : ℕ) (p : ℝ × (R3 × ℝ)) (x : R3) :
    coefficientValue n (referenceNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData n p) x =
      referenceNormalDriftFunction g L Φ H w (p,x) :=
  coefficientValue_commonSupportCoefficientFamily n (referenceNormalDriftFunction g L Φ H w)
    (contDiff_referenceNormalDriftFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p x

lemma smoothSphereValue_referenceNormalDriftJetsFamily_eq_native (p : ℝ × (R3 × ℝ)) :
    smoothSphereValue (nativeH2CoefficientSmoothData
      (referenceNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 3 p)) =
    nativeNormalDriftCoefficient (nativeSupportedDriftSmoothData
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.comp
        (contDiff_const.prodMk contDiff_id))) := by
  ext x
  have hv := coefficientValue_referenceNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 3 p (x : R3)
  change coefficientValue 3 (referenceNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 3 p) (x : R3) = _
  rw [hv]
  simp only [referenceNormalDriftFunction,nativeNormalDriftCoefficient,
    ContinuousMap.sum_apply,ContinuousMap.mul_apply,sphereCoordinate,smoothSphereValue,
    ContinuousMap.coe_mk,nativeSupportedDriftSmoothData]
  rfl

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceNormalDriftThreeHalfMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 3 p)

def referenceNormalDriftHalfMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 2 p)

lemma contDiff_referenceNormalDriftThreeHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceNormalDriftFunction g L Φ H w)
    (contDiff_referenceNormalDriftFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)

lemma contDiff_referenceNormalDriftHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceNormalDriftFunction g L Φ H w)
    (contDiff_referenceNormalDriftFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)

lemma referenceNormalDriftMultiplier_high_half_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceNormalDriftHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 _ _
    (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
      (referenceNormalDriftFunction g L Φ H w)
      (contDiff_referenceNormalDriftFunction g L y0 Φ B ε C ρ H a w hData)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalDriftFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalDriftFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalDriftFunction_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceNormalDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSphereValue_referenceNormalDriftJetsFamily_eq_native
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalDriftThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalDriftHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalDriftThreeHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceNormalDriftHalfMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNormalDriftMultiplier_high_half_compatibility
