import Calderon.ActualReferenceRotationRadialCompatibility
import Calderon.ActualReferenceTwoAngleStrongBoundaryTrace
import Calderon.ActualReferenceTwoAngleTangentBoundaryCoefficients
import Calderon.NativeH2ConormalCoefficientRadialConversion

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeFullSharpHalfTrace NativeCoefficientBoundaryMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceTwoAngleHighConormal_negative_eq_normal_add_tangent
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD
      (ordinaryConormalTraceL hcalc τ0
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
        (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
          (harmonicLiftCompletion hF f)))) =
    referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j k l t
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 i j k l t f)) +
    ∑ d : Fin 3, referenceTwoAngleTangentBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j k l d t (sphereTangentialDerivativeL hF hO hD d
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)) := by
  let U := referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
    (harmonicLiftCompletion hF f)
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  let A := referenceTwoAngleNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t
  let T := fun d => referenceTwoAngleTangentCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l d t
  let BN := referenceTwoAngleNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
    hcalc hF hO hD τ0 i j k l t
  have hNative := nativeH2_conormal_negativeHalf_eq_coefficient_normal_add_tangent
    hcalc hF hO hD τ0 F A T
    (coefficientSmoothData_referenceTwoAngleNormalJets_eq_boundaryData
      g L y0 Φ B ε C ρ H a w hData i j k l t)
    (fun d => coefficientSmoothData_referenceTwoAngleTangentJets_eq_boundaryData
      g L y0 Φ B ε C ρ H a w hData i j k l d t) U
  have hTrace := nativeHalfTraceL_firstOrder_referenceTwoAngleHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hStrong f
  have hOutward := nativeHalfOutwardTraceL_negative_inclusion hcalc hF hO hD τ0 U
  have hNormal := congrArg BN hOutward.symm
  have hTangent := congrArg (fun b : SphereSobolev (1/2:ℝ) =>
    ∑ d : Fin 3, nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (T d)
      (sphereTangentialDerivativeL hF hO hD d b)) hTrace
  exact hNative.trans (congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x+y) hNormal hTangent)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHighConormal_negative_eq_normal_add_tangent
