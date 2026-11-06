import Calderon.ActualReferenceStrongRoom
import Calderon.ActualReferenceStrongEnergy
import Calderon.OrdinaryWeightedDriftEnergy
import Calderon.DriftRegularityBootstrap

/-! Actual inverse projection and cross-order equality. Both native
strong solutions solve the same actual energy equation; coercive uniqueness
identifies their BallH1Zero fields. -/
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

theorem referenceStrongDriftFamily_inverse_isWeakSolution
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (s : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)‖ ≤ lam/4)
    (f : BallSobolev s) :
    TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f)
      (strongDirichletProjectionL s
        ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse f)) := by
  intro v
  let U : StrongDirichletSpace s :=
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse f
  have hProjection := strongDirichletProjectionL_apply s U
  have hEnergy := congrArg
    (fun u : BallH1 => TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      u (v : BallH1)) hProjection
  have hNative := referenceStrongDriftFamily_inverse_energy
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q p lam Lam hUE hsmall f v
  exact hEnergy.trans hNative

theorem referenceStrongDriftFamily_inverse_firstOrder_eq
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (s t : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)‖ ≤ lam/4)
    (f : BallSobolev s) (F : BallSobolev t)
    (hValue : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f = TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) t F) :
    strongDirichletProjectionL s
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse f) =
    strongDirichletProjectionL t
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p).inverse F) := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  have hm : AEStronglyMeasurable (fun z => a ((q,p),z))
      ((volume : Measure R3).restrict ballOpens) :=
    (h.1.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hb : AEStronglyMeasurable
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z))
      ((volume : Measure R3).restrict ballOpens) :=
    (hData.2.2.2.1.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  let hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (a ((q,p),z)) (conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    unitBall_smallDrift_energy_memLp hUE hm hb hsmall
  let hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens) hcoeff) :=
    isCoercive_unitBall_smallDrift hUE hm hb hsmall hcoeff
  have hs := referenceStrongDriftFamily_inverse_isWeakSolution
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q p lam Lam hUE hsmall f
  have ht := referenceStrongDriftFamily_inverse_isWeakSolution
    g L y0 Φ B ε C ρ H a w hData hcalc hreg t q p lam Lam hUE hsmall F
  have ht' : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f)
      (strongDirichletProjectionL t
        ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q p).inverse F)) := by
    intro v
    exact (ht v).trans (congrArg (fun x : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) x v) hValue.symm)
  exact (TauCeti.PDE.eq_weakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) hcoeff hc hs).trans
    (TauCeti.PDE.eq_weakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) hcoeff hc ht').symm

theorem exists_reference_commonRadius_allOrder_inverse_consistent
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) :
    ∃ lam Lam delta : ℝ, 0 < lam ∧ 0 < delta ∧ delta ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ delta →
        UnitBallSmallDriftData (fun z => a ((q,(y,r)),z))
          (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)) lam ∧
        (∀ s : ℕ,
          (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)).IsInvertible) ∧
        ∀ (s t : ℕ) (f : BallSobolev s) (F : BallSobolev t),
          TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f = TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) t F →
          strongDirichletProjectionL s
            ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)).inverse f) =
          strongDirichletProjectionL t
            ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc t q (y,r)).inverse F) := by
  have hWeakRoom := exists_reference_commonRadius_weakDriftData
    g L y0 Φ B ε C ρ H a w hData
  rcases hWeakRoom with ⟨lam,Lam,delta,hlam,hd,hdρ,hUE,hWeak⟩
  refine ⟨lam,Lam,delta,hlam,hd,hdρ,?_⟩
  intro q hq y hy r hr
  have hrρ : |r| ≤ ρ := hr.trans hdρ
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hp : (q,(y,r)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ) :=
    ⟨hq,hyBall,abs_le.mp hrρ⟩
  have hPointUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,(y,r)),z)) lam Lam := hUE _ hp
  have hPointWeak : UnitBallSmallDriftData (fun z => a ((q,(y,r)),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)) lam :=
    hWeak q hq y hy r hr
  have hPointSmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)‖ ≤ lam/4 :=
    hPointWeak.1
  refine ⟨hPointWeak,?_,?_⟩
  · intro s
    exact referenceStrongDriftFamily_isInvertible_of_smallDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg s q (y,r) lam Lam hPointUE hPointSmall
  · intro s t f F hValue
    exact referenceStrongDriftFamily_inverse_firstOrder_eq
      g L y0 Φ B ε C ρ H a w hData hcalc hreg s t q (y,r) lam Lam hPointUE hPointSmall f F hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
