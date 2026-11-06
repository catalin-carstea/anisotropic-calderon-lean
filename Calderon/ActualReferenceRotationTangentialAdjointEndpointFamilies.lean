import Calderon.ActualReferenceTangentialAdjointOrderOne
import Calderon.ActualReferenceRotationCoefficientJets
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
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (iA jA : Fin 3)

def referenceRotationTangentRotationJetsFamily (n : ℕ) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a) i j)
    (contDiff_tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).1 i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (tangentRotationCoefficientFunction_support (coordinateRotationPrincipalFamily iA jA a) (closedBall (0 : R3) 3)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).2 i j) t

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceRotationTangentialAdjointThreeHalfFamily (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeCoefficientRotationAdjointEndpointL (3/2:ℝ)
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceRotationTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 3 i j t)) j i

def referenceRotationTangentialAdjointHalfFamily (t : ℝ × (ℝ × (R3 × ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, nativeCoefficientRotationAdjointEndpointL (1/2:ℝ)
    (nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceRotationTangentRotationJetsFamily g L y0 Φ B ε C ρ H a w hData iA jA 2 i j t)) j i

lemma contDiff_referenceRotationTangentialAdjointThreeHalfFamily :
    ContDiff ℝ ∞ (referenceRotationTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0) := by
  unfold referenceRotationTangentialAdjointThreeHalfFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeCoefficientRotationAdjointEndpointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a) i j)
      (contDiff_tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a)
        (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support (coordinateRotationPrincipalFamily iA jA a) (closedBall (0 : R3) 3)
        (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).2 i j))).neg

lemma contDiff_referenceRotationTangentialAdjointHalfFamily :
    ContDiff ℝ ∞ (referenceRotationTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0) := by
  unfold referenceRotationTangentialAdjointHalfFamily
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  unfold nativeCoefficientRotationAdjointEndpointL
  exact (contDiff_const.clm_comp
    (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a) i j)
      (contDiff_tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a)
        (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).1 i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (tangentRotationCoefficientFunction_support (coordinateRotationPrincipalFamily iA jA a) (closedBall (0 : R3) 3)
        (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).2 i j))).neg

lemma referenceRotationTangentialAdjoint_high_half_compatibility (t : ℝ × (ℝ × (R3 × ℝ))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
      (referenceRotationTangentialAdjointThreeHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t) =
    (referenceRotationTangentialAdjointHalfFamily g L y0 Φ B ε C ρ H a w hData iA jA hcalc hF hO hD τ0 t).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro f
  unfold referenceRotationTangentialAdjointThreeHalfFamily referenceRotationTangentialAdjointHalfFamily
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ) => T f)
    (nativeCoefficientRotationAdjoint_high_half_compatibility hcalc hF hO hD τ0 _ _
      (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
        (tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a) i j)
        (contDiff_tangentRotationCoefficientFunction (coordinateRotationPrincipalFamily iA jA a)
          (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).1 i j)
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        (tangentRotationCoefficientFunction_support (coordinateRotationPrincipalFamily iA jA a) (closedBall (0 : R3) 3)
          (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData iA jA).2 i j) t) j i)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationTangentRotationJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationTangentialAdjointThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationTangentialAdjointHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationTangentialAdjointThreeHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationTangentialAdjointHalfFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationTangentialAdjoint_high_half_compatibility
