import Calderon.UniformSmallDriftCoercivity
import Calderon.NormalizedConformalDrift
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Gradient ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def weightedLinearRadialDrift (w : (R3 × ℝ) × R3 → ℝ)
    (b : (R3 × ℝ) × R3 → R3) (L : ℝ) (p : (R3 × ℝ) × R3) : R3 :=
  (-L*p.1.2) • (w p • b p)

theorem contDiff_weightedLinearRadialDrift
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b) (L : ℝ) :
    ContDiff ℝ ∞ (weightedLinearRadialDrift w b L) :=
  (contDiff_const.mul (contDiff_snd.comp contDiff_fst)).smul (hw.smul hb)

theorem weightedLinearRadialDrift_zero
    (w : (R3 × ℝ) × R3 → ℝ) (b : (R3 × ℝ) × R3 → R3)
    (L : ℝ) (y z : R3) : weightedLinearRadialDrift w b L ((y,0),z)=0 := by
  simp [weightedLinearRadialDrift]

theorem weightedLinearRadialDrift_eq_normalizedConformalDrift
    (H : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (Theta : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (w : (R3 × ℝ) × R3 → ℝ) (L : ℝ) (p : (R3 × ℝ) × R3) :
    weightedLinearRadialDrift w (normalizedConformalDriftBase H Theta F) L p =
      w p • normalizedConformalDrift H Theta F L p := by
  simp only [weightedLinearRadialDrift,normalizedConformalDrift,smul_smul,mul_comm]

theorem exists_compact_weightedLinearRadialDrift_bound
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (L : ℝ) (q : Set ((R3 × ℝ) × R3)) (hq : IsCompact q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q, ‖weightedLinearRadialDrift w b L p‖ ≤ C*|p.1.2| := by
  obtain ⟨B,hB⟩ := hq.exists_bound_of_continuousOn (hw.smul hb).continuous.continuousOn
  refine ⟨|L| * max B 0,mul_nonneg (abs_nonneg _) (le_max_right _ _),?_⟩
  intro p hp
  calc
    _ = |L| * |p.1.2| * ‖w p • b p‖ := by
      simp only [weightedLinearRadialDrift,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
    _ ≤ |L| * |p.1.2| * max B 0 := mul_le_mul_of_nonneg_left
      ((hB p hp).trans (le_max_left _ _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

theorem exists_compact_smallRadius_weightedDrift_coercivity
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b) (L : ℝ)
    (q : Set R3) (hq : IsCompact q) (eta lam Lam : ℝ) (heta : 0 < eta) (hlam : 0 < lam)
    (hUE : ∀ p ∈ q ×ˢ Icc (-eta) eta, TauCeti.PDE.UniformlyEllipticOn
      (ballOpens : Set R3) (fun z => a (p,z)) lam Lam) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      ∀ p ∈ q ×ˢ Icc (-delta) delta,
        (∀ z ∈ (ballOpens : Set R3), ‖weightedLinearRadialDrift w b L (p,z)‖ ≤ lam/4) ∧
        (3*lam/40 > 0) ∧
        (∀ u : BallH1Zero, (3*lam/40)*‖u‖*‖u‖ ≤
          TauCeti.PDE.energyFormH1 (fun z => a (p,z)) (fun z => weightedLinearRadialDrift w b L (p,z)) 0 (u : BallH1) (u : BallH1)) ∧
        (∃ hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a (p,z)) (weightedLinearRadialDrift w b L (p,z)) 0) ⊤
          ((volume : Measure R3).restrict ballOpens),
          IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) ∧
          ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤ 40/(3*lam)) ∧
        ∀ f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
          ∃! u : BallH1Zero, TauCeti.PDE.IsWeakSolutionDirichlet
            (fun z => a (p,z)) (fun z => weightedLinearRadialDrift w b L (p,z)) 0 f u ∧ ‖u‖ ≤ (40/(3*lam))*‖f‖ := by
  let S : Set ((R3 × ℝ) × R3) :=
    (q ×ˢ Icc (-eta) eta) ×ˢ closedBall (0 : R3) 1
  have hS : IsCompact S :=
    (hq.prod (isCompact_Icc : IsCompact (Icc (-eta) eta))).prod
      (isCompact_closedBall (0 : R3) 1)
  have hboundExists : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S,
      ‖weightedLinearRadialDrift w b L p‖ ≤ C * |p.1.2| :=
    exists_compact_weightedLinearRadialDrift_bound w hw b hb L S hS
  obtain ⟨C,hC,hbound⟩ := hboundExists
  have hB (p : R3 × ℝ) (hp : p ∈ q ×ˢ Icc (-eta) eta) (z : R3)
      (hz : z ∈ (ballOpens : Set R3)) : ‖weightedLinearRadialDrift w b L (p,z)‖ ≤ C*|p.2| :=
    hbound (p,z) ⟨hp,by simpa only [coe_ballOpens] using Metric.ball_subset_closedBall hz⟩
  exact exists_uniform_smallRadius_drift_coercivity a ha (weightedLinearRadialDrift w b L)
    (contDiff_weightedLinearRadialDrift w hw b hb L) q eta lam Lam C heta hlam hC hUE hB
end OAI.AnisotropicCalderon.DirichletFamily
