import Calderon.ActualReferenceAdjointH3LowerCoherence
import Calderon.ActualReferenceAdjointStrongInverse

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

def referenceAdjointStrongDirichletFamilyOne
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) :
    StrongDirichletSpace 1 →L[ℝ] BallSobolev 1 :=
  (referenceAdjointOrdinaryStrongFamilyOne
    g L y0 Φ B ε C ρ H a w hData hcalc p).comp
      (strongDirichletSubmodule 1).toSubmodule.subtypeL

lemma nativeLowerOrder_mem_strongDirichlet_zero
    (U : StrongDirichletSpace 1) :
    nativeLowerOrderL 2 (U : BallSobolev 3) ∈ strongDirichletSubmodule 0 := by
  apply (mem_strongDirichletSubmodule 0 _).mpr
  change TauCeti.Wkp.firstOrder 1 (nativeLowerOrderL 2 (U : BallSobolev 3)) ∈
    TauCeti.w1p0Submodule volume ballOpens 2
  change TauCeti.Wkp.firstOrder 2 (U : BallSobolev 3) ∈
    TauCeti.w1p0Submodule volume ballOpens 2
  exact U.2

lemma value_referenceAdjointStrongDirichletFamilyOne_eq_zero
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (U : StrongDirichletSpace 1) :
    TauCeti.Wkp.value 1
      (referenceAdjointStrongDirichletFamilyOne
        g L y0 Φ B ε C ρ H a w hData hcalc p U) =
    TauCeti.Wkp.value 0
      (referenceAdjointStrongDirichletFamily
        g L y0 Φ B ε C ρ H a w hData hcalc p
          ⟨nativeLowerOrderL 2 (U : BallSobolev 3),
            nativeLowerOrder_mem_strongDirichlet_zero U⟩) := by
  exact value_referenceAdjointOrdinaryStrongFamilyOne_eq_zero
    g L y0 Φ B ε C ρ H a w hData hcalc p U

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
