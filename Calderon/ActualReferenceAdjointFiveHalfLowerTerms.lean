import Calderon.NativeFiveHalfRotationAdjointCompatibility
import Calderon.ActualReferenceNormalDriftEndpointFamilies
import Calderon.ActualReferenceTangentialAdjointEndpointFamilies
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier NativeFiveHalfCoefficientMultiplier
attribute [local irreducible] nativeFiveHalfCoefficientMulL nativeThreeHalfCoefficientMulL
  nativeCoefficientRotationAdjointEndpointL

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceNormalDriftFiveHalfMultiplierFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (5/2:ℝ) :=
  nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceNormalDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 4 p)

lemma contDiff_referenceNormalDriftFiveHalfMultiplierFamily :
    ContDiff ℝ ∞ (referenceNormalDriftFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
  contDiff_nativeFiveHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
    (referenceNormalDriftFunction g L Φ H w)
    (contDiff_referenceNormalDriftFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)

lemma referenceNormalDriftMultiplier_fivehalf_threehalf_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).comp
      (referenceNormalDriftFiveHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceNormalDriftThreeHalfMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 _ _
    (coefficientValue_commonSupportCoefficientFamily_order_eq 4 3
      (referenceNormalDriftFunction g L Φ H w)
      (contDiff_referenceNormalDriftFunction g L y0 Φ B ε C ρ H a w hData)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceNormalDriftFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p) u

def referenceTangentialAdjointFiveHalfFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeCoefficientRotationAdjointEndpointL (5/2:ℝ)
    (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 4 i j p)) j i

lemma contDiff_referenceTangentialAdjointFiveHalfFamily :
    ContDiff ℝ ∞ (referenceTangentialAdjointFiveHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceTangentialAdjointFiveHalfFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeCoefficientRotationAdjointEndpointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeFiveHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j))).neg

lemma referenceTangentialAdjoint_fivehalf_threehalf_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (referenceTangentialAdjointFiveHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  unfold referenceTangentialAdjointFiveHalfFamily referenceTangentialAdjointThreeHalfFamily
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he := nativeCoefficientRotationAdjoint_fivehalf_threehalf_compatibility hcalc hF hO hD τ0 _ _
      (coefficientValue_commonSupportCoefficientFamily_order_eq 4 3
        (tangentRotationCoefficientFunction a i j)
        (contDiff_tangentRotationCoefficientFunction a
          (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
          (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p) j i
  exact DFunLike.congr_fun he f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
