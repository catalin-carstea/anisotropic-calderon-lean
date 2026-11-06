import Calderon.ActualAdjointNativeH3LiftOfH2Inverse
import Calderon.ActualReferenceAdjointH3Operator
import Calderon.ActualReferenceAdjointStrongInverse
import Calderon.NativeSupportedAdjointH2Regularity
import Calderon.ActualReferenceAdjointH3CoefficientFacts

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-- The actual H² inverse solution for one H¹ datum has an H³ representative
of the SAME first-order Dirichlet field. The full adjoint drift and mass are used. -/
theorem exists_referenceAdjointH3_native_lift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (p : ℝ × (R3 × ℝ))
    (hA0 : (referenceAdjointStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : BallSobolev 1) :
    ∃ U : BallSobolev 3,
      TauCeti.Wkp.firstOrder 2 U =
        ((strongDirichletProjectionL 0
          ((nativeSupportedAdjointStrongDirichletL hcalc
            (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p) 0
            (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
            (SpatialJetFields.contDiff_spatial_slice _
              (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p)
            (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
            ((jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p)).inverse
              (nativeLowerOrderL 0 f))) : BallH1) := by
  let F := referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p
  let M1 := referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p
  let M2 := referenceAdjointMassJetsFamilyTwo g L y0 Φ B ε C ρ H a w hData p
  let beta : R3 → R3 := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)
  let hb : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1 p
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  let hz : ∀ x, x ∉ K → beta x = 0 :=
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 p
  have hNative : (nativeSupportedAdjointStrongDirichletL
      hcalc F 0 beta hb K hK hz).IsInvertible := by
    rw [← referenceAdjointStrongDirichletFamily_eq_native
      g L y0 Φ B ε C ρ H a w hData hcalc p]
    exact hA0
  have hM : coefficientValue 2 M2 = coefficientValue 1 M1 :=
    coefficientValue_referenceAdjointMassJetsFamilyTwo_eq_one
      g L y0 Φ B ε C ρ H a w hData p
  have hMassValue : coefficientValue 1 M1 =
      fun x => coefficientValue 1 (0 : SmoothCoefficientJets 1) x -
        nativeSupportedDriftDivergence beta x :=
    coefficientValue_referenceAdjointMassJetsFamily_eq_native_zero
      g L y0 Φ B ε C ρ H a w hData p
  obtain ⟨lam,Lam,hUEF⟩ := exists_referenceJointPrincipalJetsFamily_elliptic
    g L y0 Φ B ε C ρ H a w hData p
  exact exists_nativeAdjoint_H3_lift_of_H2_inverse
    hcalc hreg F lam Lam hUEF 0 M1 M2 beta hb K hK hz
    hMassValue hM hNative f

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
