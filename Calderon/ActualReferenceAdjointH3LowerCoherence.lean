import Calderon.ActualReferenceAdjointH3PrincipalCoherence
import Calderon.ActualReferenceAdjointH3MassCoherence
import Calderon.ActualHarmonicLiftConsistency
import Calderon.ActualReferencePrincipalGlobalEllipticity

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

private lemma value_sub (s : ℕ) (X Y : BallSobolev s) :
    TauCeti.Wkp.value s (X-Y) =
      TauCeti.Wkp.value s X - TauCeti.Wkp.value s Y := by
  change (TauCeti.Wkp.valueL s) (X-Y) =
    (TauCeti.Wkp.valueL s) X - (TauCeti.Wkp.valueL s) Y
  exact map_sub _ X Y

/-- Exact lowering of the SAME full formal adjoint, including the drift and
negative-divergence mass, from H³→H¹ to the established H²→L² family. -/
theorem value_referenceAdjointOrdinaryStrongFamilyOne_eq_zero
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) (U : BallSobolev 3) :
    TauCeti.Wkp.value 1
      (referenceAdjointOrdinaryStrongFamilyOne
        g L y0 Φ B ε C ρ H a w hData hcalc p U) =
      TauCeti.Wkp.value 0
        (referenceAdjointOrdinaryStrongFamily
          g L y0 Φ B ε C ρ H a w hData hcalc p (nativeLowerOrderL 2 U)) := by
  let F3 := referenceJointPrincipalJetsFamilyThree g L y0 Φ B ε C ρ H a w hData p
  let F2 := referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p
  let M2 := referenceAdjointMassJetsFamilyTwo g L y0 Φ B ε C ρ H a w hData p
  let M1 := referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p
  let E := nativeLowerOrderL 2 U
  have hF : coefficientMatrixField 3 F3 = coefficientMatrixField 2 F2 := by
    exact (coefficientMatrixField_referenceJointPrincipalJetsFamilyThree
      g L y0 Φ B ε C ρ H a w hData p).trans
      (coefficientMatrixField_referenceJointPrincipalJetsFamily
        g L y0 Φ B ε C ρ H a w hData p).symm
  have hFT : coefficientMatrixField 3 (fun i j => F3 j i) =
      coefficientMatrixField 2 (nativePrincipalTransposeJets F2) := by
    exact congrArg (fun A : MatrixField => fun x => (A x)ᵀ) hF
  have hM : coefficientValue 2 M2 = coefficientValue 1 M1 := by
    funext x
    exact (coefficientValue_referenceAdjointMassJetsFamilyTwo
      g L y0 Φ B ε C ρ H a w hData p x).trans
      (coefficientValue_referenceAdjointMassJetsFamily
        g L y0 Φ B ε C ρ H a w hData p x).symm
  have hPT := value_ordinaryPrincipalL_one_eq_zero_of_same_matrix
    hcalc (fun i j => F3 j i) (nativePrincipalTransposeJets F2) hFT U
  have hP := value_ordinaryPrincipalL_one_eq_zero_of_same_matrix hcalc F3 F2 hF U
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic
    g L y0 Φ B ε C ρ H a w hData p
  have hFirst : TauCeti.Wkp.firstOrder 2 U = TauCeti.Wkp.firstOrder 1 E := rfl
  have hD := referenceOrdinaryStrongDriftFamily_value_eq_of_firstOrder_eq
    g L y0 Φ B ε C ρ H a w hData hcalc 1 0 p.1 p.2 lam Lam hUE U E hFirst
  have hMass := value_adjointMass_one_eq_zero_of_same_coefficient
    hcalc M2 M1 hM E
  change TauCeti.Wkp.value 1
      (ordinaryPrincipalL hcalc 1 (fun i j => F3 j i) U +
        (ordinaryPrincipalL hcalc 1 F3 U -
          referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2 U) +
        coefficientMultiplier hcalc 1 M2 (nativeLowerOrderL 1 E)) =
    TauCeti.Wkp.value 0
      (ordinaryPrincipalL hcalc 0 (nativePrincipalTransposeJets F2) E +
        (ordinaryPrincipalL hcalc 0 F2 E -
          referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2 E) +
        nativeCoefficientMassL hcalc M1 (nativeH2FirstOrderL E))
  rw [TauCeti.Wkp.value_add]
  rw [TauCeti.Wkp.value_add]
  rw [value_sub]
  rw [TauCeti.Wkp.value_add]
  rw [TauCeti.Wkp.value_add]
  rw [value_sub]
  exact congrArg₂ (fun x y => x+y)
    (congrArg₂ (fun x y => x+y) hPT (congrArg₂ (fun x y => x-y) hP hD)) hMass

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
