import Calderon.ActualReferenceAdjointH3Operator
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
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma coefficientValue_referenceAdjointMassJetsFamilyTwo_eq_one
    (p : ℝ × (R3 × ℝ)) :
    coefficientValue 2 (referenceAdjointMassJetsFamilyTwo
      g L y0 Φ B ε C ρ H a w hData p) =
      coefficientValue 1 (referenceAdjointMassJetsFamily
        g L y0 Φ B ε C ρ H a w hData p) := by
  funext x
  exact (coefficientValue_referenceAdjointMassJetsFamilyTwo
    g L y0 Φ B ε C ρ H a w hData p x).trans
    (coefficientValue_referenceAdjointMassJetsFamily
      g L y0 Φ B ε C ρ H a w hData p x).symm

lemma coefficientValue_referenceAdjointMassJetsFamily_eq_native_zero
    (p : ℝ × (R3 × ℝ)) :
    coefficientValue 1 (referenceAdjointMassJetsFamily
      g L y0 Φ B ε C ρ H a w hData p) =
      fun x => coefficientValue 1 (0 : SmoothCoefficientJets 1) x -
        nativeSupportedDriftDivergence
          (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x := by
  funext x
  have hzero : coefficientValue 1 (0 : SmoothCoefficientJets 1) x = 0 := rfl
  rw [hzero,zero_sub]
  exact coefficientValue_referenceAdjointMassJetsFamily
    g L y0 Φ B ε C ρ H a w hData p x

lemma exists_referenceJointPrincipalJetsFamily_elliptic
    (p : ℝ × (R3 × ℝ)) :
    ∃ lam Lam : ℝ,
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (coefficientMatrixField 2
          (referenceJointPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData p))
        lam Lam := by
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic
    g L y0 Φ B ε C ρ H a w hData p
  refine ⟨lam,Lam,?_⟩
  rw [coefficientMatrixField_referenceJointPrincipalJetsFamily]
  exact hUE

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
