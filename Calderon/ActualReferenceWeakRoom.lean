import Calderon.JointConformalReferenceFramedDriftData
import Calderon.CompactParameterReferenceWeakDriftCoercivity

/-! Actual retained-witness common weak radius. No Sobolev order enters
the radius choice and no desired inverse estimate is assumed. -/
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

theorem exists_reference_commonRadius_weakDriftData :
    ∃ lam Lam delta : ℝ, 0 < lam ∧ 0 < delta ∧ delta ≤ ρ ∧
      (∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ),
        TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
          (fun z => a (p,z)) lam Lam) ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ delta →
        UnitBallSmallDriftData (fun z => a ((q,(y,r)),z))
          (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,r)),z)) lam := by
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
  refine ⟨lam,Lam,delta,hlam,hd,hdρ,hUE,?_⟩
  intro q hq y hy r hr
  exact hWeak ((q,y),r)
    ⟨⟨hq,by simpa only [mem_closedBall,dist_eq_norm] using hy⟩,abs_le.mp hr⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
