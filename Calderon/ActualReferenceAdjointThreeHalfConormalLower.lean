import Calderon.ActualReferenceAdjointThreeHalfConormalTrace
import Calderon.ActualReferenceAdjointSharpConormalFamily
import Calderon.NativeH3CoefficientConormalTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeH3CoefficientConormalTrace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma coefficientValue_referenceJointPrincipalJetsFamilyThree_transpose_eq_two
    (p : ℝ × (R3 × ℝ)) (i j : Fin 3) :
    coefficientValue 3
      (referenceJointPrincipalJetsFamilyThree
        g L y0 Φ B ε C ρ H a w hData p j i) =
    coefficientValue 2
      (nativePrincipalTransposeJets
        (referenceJointPrincipalJetsFamily
          g L y0 Φ B ε C ρ H a w hData p) i j) := by
  funext x
  have h3 := congrArg (fun F : MatrixField => F x j i)
    (coefficientMatrixField_referenceJointPrincipalJetsFamilyThree
      g L y0 Φ B ε C ρ H a w hData p)
  have h2 := congrArg (fun F : MatrixField => F x j i)
    (coefficientMatrixField_referenceJointPrincipalJetsFamily
      g L y0 Φ B ε C ρ H a w hData p)
  exact h3.trans h2.symm

/-- The new H³ conormal trace lowers exactly to the existing H² adjoint
conormal trace on the same bulk field and same coefficient values. -/
theorem sphereSobolevInclusionL_referenceAdjointThreeHalfConormalTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) (U : BallSobolev 3) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (referenceAdjointThreeHalfConormalTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p U) =
    referenceAdjointSharpConormalTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (nativeLowerOrderL 2 U) := by
  exact sphereSobolevInclusionL_nativeThreeHalfCoefficientConormalTraceL
    hcalc hF hO hD τ0
    (fun i j => referenceJointPrincipalJetsFamilyThree
      g L y0 Φ B ε C ρ H a w hData p j i)
    (nativePrincipalTransposeJets
      (referenceJointPrincipalJetsFamily
        g L y0 Φ B ε C ρ H a w hData p))
    (coefficientValue_referenceJointPrincipalJetsFamilyThree_transpose_eq_two
      g L y0 Φ B ε C ρ H a w hData p) U

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
