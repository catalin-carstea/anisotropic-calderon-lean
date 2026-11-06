import Calderon.CompactParameterReferenceDrift
import Calderon.UniformSmallDriftCoercivity

/-! UNCOMPILED author proposal. EXPANSION.md D9--D10 was saved before source.
One weak radius works for the entire compact dilation/center family; no order enters its choice. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open ConnectionError NormalCoordinatesFrame MetricOperator EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def UnitBallSmallDriftData
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (beta : R3 → R3) (lam : ℝ) : Prop :=
  (∀ z ∈ (ballOpens : Set R3), ‖beta z‖ ≤ lam/4) ∧
  (3*lam/40 > 0) ∧
  (∀ u : BallH1Zero, (3*lam/40)*‖u‖*‖u‖ ≤
    TauCeti.PDE.energyFormH1 a beta 0 (u : BallH1) (u : BallH1)) ∧
  (∃ hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (beta z) 0) ⊤
    ((volume : Measure R3).restrict ballOpens),
    IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) ∧
    ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤ 40/(3*lam)) ∧
  ∀ f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
    ∃! u : BallH1Zero, TauCeti.PDE.IsWeakSolutionDirichlet a beta 0 f u ∧
      ‖u‖ ≤ (40/(3*lam))*‖f‖

theorem exists_uniform_smallRadius_parameter_drift_coercivity
    (a : (P × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (beta : (P × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ beta)
    (Q : Set P) (eta lam Lam D : ℝ) (heta : 0 < eta) (hlam : 0 < lam) (hD : 0 ≤ D)
    (hUE : ∀ p ∈ Q ×ˢ Icc (-eta) eta, TauCeti.PDE.UniformlyEllipticOn
      (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hbound : ∀ p ∈ Q ×ˢ Icc (-eta) eta, ∀ z ∈ (ballOpens : Set R3),
      ‖beta (p,z)‖ ≤ D*|p.2|) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      ∀ p ∈ Q ×ˢ Icc (-delta) delta,
        UnitBallSmallDriftData (fun z => a (p,z)) (fun z => beta (p,z)) lam := by
  let delta := min eta (lam/(4*(D+1)))
  have hd : 0 < delta := lt_min heta (by positivity)
  refine ⟨delta,hd,min_le_left _ _,?_⟩
  intro p hp
  have hpE : p ∈ Q ×ˢ Icc (-eta) eta :=
    ⟨hp.1,⟨by linarith [hp.2.1,min_le_left eta (lam/(4*(D+1)))],
      by linarith [hp.2.2,min_le_left eta (lam/(4*(D+1))) ]⟩⟩
  have hsmall (z : R3) (hz : z ∈ (ballOpens : Set R3)) : ‖beta (p,z)‖ ≤ lam/4 := by
    calc
      _ ≤ D*|p.2| := hbound p hpE z hz
      _ ≤ (D+1)*|p.2| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (D+1)*(lam/(4*(D+1))) := mul_le_mul_of_nonneg_left
        ((abs_le.mpr hp.2).trans (min_le_right _ _)) (by positivity)
      _ = lam/4 := by field_simp [ne_of_gt (show 0 < D+1 by linarith)]
  have hm : AEStronglyMeasurable (fun z => a (p,z)) ((volume : Measure R3).restrict ballOpens) :=
    (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbm : AEStronglyMeasurable (fun z => beta (p,z)) ((volume : Measure R3).restrict ballOpens) :=
    (hb.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  let hcoeff := unitBall_smallDrift_energy_memLp (hUE p hpE) hm hbm hsmall
  exact ⟨hsmall,by positivity,unitBall_smallDrift_coercivity (hUE p hpE) hm hbm hsmall,
    ⟨hcoeff,isCoercive_unitBall_smallDrift (hUE p hpE) hm hbm hsmall hcoeff,
      norm_unitBall_smallDrift_functionalInverse_le (hUE p hpE) hm hbm hsmall hcoeff⟩,
    existsUnique_unitBall_smallDrift_weakSolution (hUE p hpE) hm hbm hsmall⟩

theorem exists_compact_parameter_conformalReference_weak_drift_coercivity
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
      (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
      (w : (ℝ × (R3 × ℝ)) × R3 → ℝ),
      ConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w ∧
      ∃ lam Lam delta : ℝ, 0 < lam ∧ 0 < delta ∧ delta ≤ ρ ∧
        (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
          TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam) ∧
        ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ delta →
          UnitBallSmallDriftData (fun z => a ((q,(y,r)),z))
            (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)) lam := by
  obtain ⟨Φ,B,ε,C,ρ,H,a,w,hData⟩ :=
    exists_compact_parameter_conformalReference_framed_drift g hg L y0
  have hSaved : ConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w := hData
  rcases hData with
    ⟨hOld,hBase,hDrift,hBeta,hAidentity,hBetaValue,hBetaSupport,hZero,hJets,hJetsNormalized,
      hMetric,hMixedD,hMixedBeta,hFullBounds⟩
  rcases hOld with
    ⟨hNormal,hρ,hρε,hHDef,haDef,hwDef,hH,hPos,ha,hw,hSupport,hLocal,hZeroJet,hUEExists,hMixed⟩
  obtain ⟨lam,Lam,hUEClosed⟩ := hUEExists
  have hBaseParam : (0,(y0,(0 : ℝ))) ∈
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ) :=
    ⟨⟨le_rfl,by norm_num⟩,mem_closedBall_self hρ.le,⟨by linarith,hρ.le⟩⟩
  have hlam : 0 < lam := (hUEClosed (0,(y0,0)) hBaseParam).1
  have hUE : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a (p,z)) lam Lam := by
    intro p hp
    refine ⟨(hUEClosed p hp).1,(hUEClosed p hp).2.1,?_⟩
    intro z hz
    exact (hUEClosed p hp).2.2
      (by simpa only [coe_ballOpens] using Metric.ball_subset_closedBall hz)
  obtain ⟨D,hD,hFull,hLinear⟩ := hFullBounds 0
  let Q : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ
  let A : ((ℝ × R3) × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun p => a ((p.1.1.1,(p.1.1.2,p.1.2)),p.2)
  let beta : ((ℝ × R3) × ℝ) × R3 → R3 :=
    fun p => conformalReferenceWeightedFramedDrift g L Φ H w
      ((p.1.1.1,(p.1.1.2,p.1.2)),p.2)
  have hc : ContDiff ℝ ∞
      (fun p : ((ℝ × R3) × ℝ) × R3 => ((p.1.1.1,(p.1.1.2,p.1.2)),p.2)) :=
    (contDiff_fst.fst.fst.prodMk (contDiff_fst.fst.snd.prodMk contDiff_fst.snd)).prodMk contDiff_snd
  have hA : ContDiff ℝ ∞ A := ha.comp hc
  have hbeta : ContDiff ℝ ∞ beta := hBeta.comp hc
  have hUEQ : ∀ p ∈ Q ×ˢ Icc (-ρ) ρ,
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => A (p,z)) lam Lam := by
    intro p hp
    exact hUE (p.1.1,(p.1.2,p.2)) ⟨hp.1.1,hp.1.2,hp.2⟩
  have hBound : ∀ p ∈ Q ×ˢ Icc (-ρ) ρ, ∀ z ∈ (ballOpens : Set R3),
      ‖beta (p,z)‖ ≤ D*|p.2| := by
    intro p hp z hz
    have hz1 : z ∈ closedBall (0 : R3) 1 :=
      by simpa only [coe_ballOpens] using Metric.ball_subset_closedBall hz
    have hz2 : z ∈ closedBall (0 : R3) 2 :=
      closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz1
    exact (hLinear ((p.1.1,(p.1.2,p.2)),z) ⟨⟨hp.1.1,hp.1.2,hp.2⟩,hz2⟩).2
  obtain ⟨delta,hd,hdρ,hWeak⟩ := exists_uniform_smallRadius_parameter_drift_coercivity
    A hA beta hbeta Q ρ lam Lam D hρ hlam hD hUEQ hBound
  refine ⟨Φ,B,ε,C,ρ,H,a,w,hSaved,lam,Lam,delta,hlam,hd,hdρ,hUE,?_⟩
  intro q hq y hy r hr
  exact hWeak ((q,y),r)
    ⟨⟨hq,by simpa only [mem_closedBall,dist_eq_norm] using hy⟩,abs_le.mp hr⟩

end OAI.AnisotropicCalderon.DirichletFamily
