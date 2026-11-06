import Calderon.NativeH2ConormalOrthogonalCovariance
import Calderon.ActualReferenceRotationNormalCoefficient
import Calderon.ActualReferenceAngleConormalCovariance
import Calderon.ActualReferenceOrthogonalStrongLift
import Calderon.ActualReferenceRadialInvertibleEndpointCompatibility

/-! Expanded first in EXPANSION-actual-rotation-lower-radial-dense-covariance-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceRotationPrincipalJets_field_conjugacy (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ)) :
    coefficientMatrixField 2
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p)) =
    orthogonalPrincipalCoefficient (coordinateRotationIsometry i j θ)
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 a
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
        (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p)) := by
  rw [coefficientMatrixField_referenceRotationPrincipalJetsFamily,
    coefficientMatrixField_commonSupportMatrixFamily]
  exact funext (coordinateRotationPrincipalFamily_eq_orthogonal i j a θ p)

lemma ordinaryConormalTraceL_referenceOrthogonalStrongHarmonicLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    ordinaryConormalTraceL hcalc τ0
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p))
      (referenceOrthogonalStrongHarmonicLift g L y0 Φ B ε C ρ H a w hData
        hcalc hF (coordinateRotationIsometry i j θ) p f) =
    sphereL2OrthogonalPullback (coordinateRotationIsometry i j θ)
      (referenceConormalTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2
          (harmonicLiftCompletion hF
            (sphereSobolevOrthogonalPullbackL (3/2:ℝ) (coordinateRotationIsometry i j θ).symm f)))) := by
  rw [referenceConormalTraceFamily_joint_coefficient_eq g L y0 Φ B ε C ρ H a w hData hcalc τ0 p]
  exact ordinaryConormalTraceL_nativeH2OrthogonalPullback hcalc τ0
    (coordinateRotationIsometry i j θ) _ _
    (referenceRotationPrincipalJets_field_conjugacy g L y0 Φ B ε C ρ H a w hData i j θ p) _

lemma referenceRotationWeakConormalEndpointFamily_inclusion_eq_conormal
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceRotationWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j (θ,p)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p))
        (referenceOrthogonalStrongHarmonicLift g L y0 Φ B ε C ρ H a w hData
          hcalc hF (coordinateRotationIsometry i j θ) p f))) := by
  let e := coordinateRotationIsometry i j θ
  let f' : SphereSobolev (3/2:ℝ) := sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f
  have hcancel := sphereSobolevOrthogonalPullback_inclusion_inverse
    (3/2:ℝ) (1/2:ℝ) (by norm_num) e f
  have hcov := referenceRotationWeakConormalEndpointFamily_coordinate_covariance
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j p hWeak θ
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f')
  have hco := referenceWeakConormalEndpointFamily_eq_conormal_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2 hStrong hWeak f'
  have hflux := ordinaryConormalTraceL_referenceOrthogonalStrongHarmonicLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF τ0 i j θ p f
  change _ = sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (sphereSobolevZeroEquiv hO hD _) 
  rw [hflux,sphereSobolevZeroEquiv_orthogonalPullback,
    sphereSobolevInclusionL_orthogonalPullback_apply]
  exact ((congrArg (referenceRotationWeakConormalEndpointFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j (θ,p)) hcancel).symm.trans hcov).trans
      (congrArg (sphereSobolevOrthogonalPullbackL (-(1/2:ℝ)) e) hco)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationPrincipalJets_field_conjugacy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryConormalTraceL_referenceOrthogonalStrongHarmonicLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationWeakConormalEndpointFamily_inclusion_eq_conormal
