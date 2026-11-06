import Calderon.ActualReferenceWeakRoom
import Calderon.ActualHarmonicLiftZeroDerivative
import Calderon.WeightedDriftCommonRadius

/-! Actual same-witness all-order strong inverse on one weak room.
The native lower-order bootstrap is used; no orderwise Neumann-radius
intersection or desired invertibility premise appears in the actual-room root. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem referenceStrongDriftFamily_eq_commonSupport
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) :
    referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q =
      let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
      commonSupportStrongDriftFamily hcalc s
        (jointFixedParameterSlice a q) h.1
        (jointFixedParameterSlice w q) h.2.1
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  funext p
  exact ordinaryStrongDriftFamily_restriction hcalc s _ h.1 _ h.2.1 _ h.2.2.1
    _ (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p

theorem weightedDriftSlice_reference_eq (q : ℝ) (p : R3 × ℝ) :
    weightedDriftSlice (jointFixedParameterSlice w q)
      (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) L p =
      fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z) := by
  funext z
  change (-L*p.2) • (w ((q,p),z) •
      conformalReferenceFramedDriftBase g L Φ H ((q,p),z)) =
    w ((q,p),z) • ((-L*p.2) •
      conformalReferenceFramedDriftBase g L Φ H ((q,p),z))
  exact smul_comm _ _ _

theorem referenceStrongDriftFamily_isInvertible_of_smallDrift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (s : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)‖ ≤ lam/4) :
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).IsInvertible := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  have hRest := congrArg (fun T : R3 × ℝ → StrongDirichletSpace s →L[ℝ] BallSobolev s => T p)
    (referenceStrongDriftFamily_eq_commonSupport g L y0 Φ B ε C ρ H a w hData hcalc s q)
  change referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p =
    commonSupportStrongDriftFamily hcalc s
      (jointFixedParameterSlice a q) h.1
      (jointFixedParameterSlice w q) h.2.1
      (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p at hRest
  rw [hRest,commonSupportStrongDriftFamily_eq_supportedStrongOperatorL]
  apply supportedStrongOperatorL_isInvertible hcalc hreg s _ lam Lam
  · rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hUE
  · intro z hz
    have hBeta := congrArg (fun f : R3 → R3 => f z)
      (weightedDriftSlice_reference_eq g L y0 Φ B ε C ρ H a w hData q p)
    rw [hBeta]
    exact hsmall z hz

theorem exists_reference_commonRadius_allOrder_strongDrift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) :
    ∃ lam Lam delta : ℝ, 0 < lam ∧ 0 < delta ∧ delta ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ delta →
        UnitBallSmallDriftData (fun z => a ((q,(y,r)),z))
          (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)) lam ∧
        ∀ s : ℕ,
          (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)).IsInvertible := by
  obtain ⟨lam,Lam,delta,hlam,hd,hdρ,hUE,hWeak⟩ :=
    exists_reference_commonRadius_weakDriftData g L y0 Φ B ε C ρ H a w hData
  refine ⟨lam,Lam,delta,hlam,hd,hdρ,?_⟩
  intro q hq y hy r hr
  have hrρ : |r| ≤ ρ := hr.trans hdρ
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hp : (q,(y,r)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ) :=
    ⟨hq,hyBall,abs_le.mp hrρ⟩
  have hweak := hWeak q hq y hy r hr
  refine ⟨hweak,?_⟩
  intro s
  exact referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q (y,r) lam Lam (hUE _ hp) hweak.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
