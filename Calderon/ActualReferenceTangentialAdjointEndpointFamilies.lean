import Calderon.ActualReferenceTangentialAdjointOrderOne
import Calderon.NativeCoefficientRotationAdjointEndpointCompatibility
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceTangentRotationJetsFamily (n : ℕ) (i j : Fin 3) (p : ℝ × (R3 × ℝ)) :
    SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (tangentRotationCoefficientFunction a i j)
    (contDiff_tangentRotationCoefficientFunction a
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
      (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceTangentialAdjointThreeHalfFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeCoefficientRotationAdjointEndpointL (3/2:ℝ)
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 3 i j p)) j i

def referenceTangentialAdjointHalfFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeCoefficientRotationAdjointEndpointL (1/2:ℝ)
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j p)) j i

lemma contDiff_referenceTangentialAdjointThreeHalfFamily :
    ContDiff ℝ ∞ (referenceTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceTangentialAdjointThreeHalfFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeCoefficientRotationAdjointEndpointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j))).neg

lemma contDiff_referenceTangentialAdjointHalfFamily :
    ContDiff ℝ ∞ (referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  unfold referenceTangentialAdjointHalfFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeCoefficientRotationAdjointEndpointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction a i j)
      (contDiff_tangentRotationCoefficientFunction a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j))).neg

lemma referenceTangentialAdjoint_high_half_compatibility (p : ℝ × (R3 × ℝ)) :
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
      (referenceTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  unfold referenceTangentialAdjointThreeHalfFamily referenceTangentialAdjointHalfFamily
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) => T f)
    (nativeCoefficientRotationAdjoint_high_half_compatibility hcalc hF hO hD τ0 _ _
      (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
        (tangentRotationCoefficientFunction a i j)
        (contDiff_tangentRotationCoefficientFunction a
          (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1 i j)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        (tangentRotationCoefficientFunction_support a (closedBall (0 : R3) 3)
          (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 i j) p) j i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentRotationJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentialAdjointThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentialAdjointHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTangentialAdjointThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTangentialAdjointHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTangentialAdjoint_high_half_compatibility
