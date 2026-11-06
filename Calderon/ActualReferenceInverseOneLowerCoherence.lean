import Calderon.ActualReferenceInverseConsistency

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-SMOOTH-MULTIPLIER-GAIN-EXPANSION-v001.md. Exact native H3/H2 inverse coherence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceStrongDriftFamily

lemma lowerOrder_referenceStrongDriftFamily_inverse_one
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)‖ ≤ lam/4)
    (F : BallSobolev 1) :
    TauCeti.Wkp.lowerOrder 2
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q p).inverse F :
        BallSobolev 3) =
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).inverse
        (TauCeti.Wkp.value 1 F) : BallSobolev 2) := by
  let U : BallSobolev 3 :=
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q p).inverse F
  let V : BallSobolev 2 :=
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).inverse
      (TauCeti.Wkp.value 1 F)
  have hProjection := referenceStrongDriftFamily_inverse_firstOrder_eq
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 1 0 q p lam Lam hUE hsmall
      F (TauCeti.Wkp.value 1 F) rfl
  have hFirst := congrArg (fun z : BallH1Zero => (z : BallH1)) hProjection
  change TauCeti.Wkp.firstOrder 2 U = TauCeti.Wkp.firstOrder 1 V at hFirst
  have hValue := congrArg TauCeti.W1p.value hFirst
  simp only [TauCeti.Wkp.value_firstOrder] at hValue
  apply TauCeti.Wkp.ext 2
  exact (TauCeti.Wkp.value_succ 2 U).symm.trans hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.lowerOrder_referenceStrongDriftFamily_inverse_one

