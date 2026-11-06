import Calderon.ActualReferenceInverseConsistency
import Calderon.NativeReferenceHarmonicBoundary
import Calderon.DirichletForcingInjectivity
import Calderon.OrdinaryWeightedDriftEnergy
import Calderon.OrdinaryStrongDriftValueConsistency

/-! Source-only exact same-extension actual harmonic lift consistency across
integer native orders, on one actual weak radius. Sharp trace-kernel and
all-real boundary interpretation remain separate. Full interfaces sealed first. -/
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

theorem referenceOrdinaryStrongDriftFamily_value_eq_of_firstOrder_eq
    (hcalc : FixedSobolevCalculus) (s t : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (E : BallSobolev (s+2)) (F : BallSobolev (t+2))
    (hFirstOrder : TauCeti.Wkp.firstOrder (s+1) E = TauCeti.Wkp.firstOrder (t+1) F) :
    TauCeti.Wkp.value s
      (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E) =
    TauCeti.Wkp.value t
      (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p F) := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  change TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (ordinaryStrongDriftFamily hcalc s (jointFixedParameterSlice a q) h.1
        (jointFixedParameterSlice w q) h.2.1
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p E) =
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) t
      (ordinaryStrongDriftFamily hcalc t (jointFixedParameterSlice a q) h.1
        (jointFixedParameterSlice w q) h.2.1
        (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
        (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p F)
  exact ordinaryStrongDriftFamily_value_eq_of_firstOrder_eq hcalc
    (jointFixedParameterSlice a q) h.1 (jointFixedParameterSlice w q) h.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2
    L p s t lam Lam hUE E F hFirstOrder


theorem referenceHarmonicLiftFamily_firstOrder_eq
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (s t : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)‖ ≤ lam/4)
    (E : BallSobolev (s+2)) (F : BallSobolev (t+2))
    (hFirstOrder : TauCeti.Wkp.firstOrder (s+1) E = TauCeti.Wkp.firstOrder (t+1) F) :
    TauCeti.Wkp.firstOrder (s+1)
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E) =
    TauCeti.Wkp.firstOrder (t+1)
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p F) := by
  have his := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q p lam Lam hUE hsmall
  have hit := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg t q p lam Lam hUE hsmall
  have hValue := referenceOrdinaryStrongDriftFamily_value_eq_of_firstOrder_eq
    g L y0 Φ B ε C ρ H a w hData hcalc s t q p lam Lam hUE E F hFirstOrder
  have hCorrection := referenceStrongDriftFamily_inverse_firstOrder_eq
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s t q p lam Lam hUE hsmall
    (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E)
    (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p F) hValue
  have hc := congrArg (fun u : BallH1Zero => (u : BallH1)) hCorrection
  change TauCeti.Wkp.firstOrder (s+1)
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse
        (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E) :
          BallSobolev (s+2)) =
    TauCeti.Wkp.firstOrder (t+1)
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p).inverse
        (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p F) :
          BallSobolev (t+2)) at hc
  rw [referenceHarmonicLiftFamily_eq_strongHarmonicProjection
      g L y0 Φ B ε C ρ H a w hData hcalc s q p his,
    referenceHarmonicLiftFamily_eq_strongHarmonicProjection
      g L y0 Φ B ε C ρ H a w hData hcalc t q p hit,
    strongHarmonicProjectionL_apply,strongHarmonicProjectionL_apply]
  change (TauCeti.Wkp.firstOrderL (s+1)) (E -
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse
        (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p E) :
          BallSobolev (s+2))) =
    (TauCeti.Wkp.firstOrderL (t+1)) (F -
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p).inverse
        (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p F) :
          BallSobolev (t+2)))
  rw [map_sub,map_sub]
  exact congrArg₂ (fun u v : BallH1 => u-v) hFirstOrder hc

theorem exists_reference_commonRadius_allOrder_harmonicLift_consistent
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ delta →
        (∀ (s : ℕ) (E : BallSobolev (s+2)),
          referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
            (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r) E) = 0) ∧
        ∀ (s t : ℕ) (E : BallSobolev (s+2)) (F : BallSobolev (t+2)),
          TauCeti.Wkp.firstOrder (s+1) E = TauCeti.Wkp.firstOrder (t+1) F →
          TauCeti.Wkp.firstOrder (s+1)
            (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r) E) =
          TauCeti.Wkp.firstOrder (t+1)
            (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q (y,r) F) := by
  obtain ⟨lam,Lam,delta,hlam,hd,hdρ,hUE,hWeak⟩ :=
    exists_reference_commonRadius_weakDriftData g L y0 Φ B ε C ρ H a w hData
  refine ⟨delta,hd,hdρ,?_⟩
  intro q hq y hy r hr
  have hrρ : |r| ≤ ρ := hr.trans hdρ
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hp : (q,(y,r)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ) :=
    ⟨hq,hyBall,abs_le.mp hrρ⟩
  have hweak := hWeak q hq y hy r hr
  constructor
  · intro s E
    have hi := referenceStrongDriftFamily_isInvertible_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg s q (y,r) lam Lam (hUE _ hp) hweak.1
    rw [referenceHarmonicLiftFamily_eq_strongHarmonicProjection
      g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r) hi]
    exact strongHarmonicProjectionL_equation s _ hi E
  · intro s t E F hFirstOrder
    exact referenceHarmonicLiftFamily_firstOrder_eq
      g L y0 Φ B ε C ρ H a w hData hcalc hreg s t q (y,r) lam Lam
      (hUE _ hp) hweak.1 E F hFirstOrder

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
