import Calderon.ActualWeakSolution
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem unitBall_smallDrift_energy_memLp
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {b : R3 → R3} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hb : AEStronglyMeasurable b ((volume : Measure R3).restrict ballOpens))
    (hbound : ∀ z ∈ (ballOpens : Set R3), ‖b z‖ ≤ lam/4) :
    MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (b z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
  TauCeti.PDE.memLp_energyIntegrand_of_bounds ha.upper_nonneg hm hb aestronglyMeasurable_const
    (fun _ hx => ha.upper_bound hx) hbound (gamma := 0) (fun _ _ => by simp)

theorem unitBall_smallDrift_coercivity
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {b : R3 → R3} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hb : AEStronglyMeasurable b ((volume : Measure R3).restrict ballOpens))
    (hbound : ∀ z ∈ (ballOpens : Set R3), ‖b z‖ ≤ lam/4) (u : BallH1Zero) :
    (3*lam/40)*‖u‖*‖u‖ ≤ TauCeti.PDE.energyFormH1 a b 0 (u : BallH1) (u : BallH1) := by
  have hp := TauCeti.W1p.norm_value_le_mul_norm_gradient_of_subset_ball
    (Omega := ballOpens) (c := (0 : R3)) (R := 1)
    (by decide : (2 : ℝ≥0∞) ≠ ⊤)
    (show (ballOpens : Set R3) ⊆ Metric.ball 0 1 from Set.Subset.rfl) u.2
  have he := ha.mul_norm_sq_le_energyFormH1_self_of_poincare hm hb aestronglyMeasurable_const
    hbound (gamma := 0) (P := 2) (fun _ _ => by simp) (fun _ _ => le_rfl)
    (u := (u : BallH1)) (by simpa using hp)
  have hconst : (lam^2-(lam/4)^2*(2:ℝ)^2)/(2*lam*((2:ℝ)^2+1)) = 3*lam/40 := by
    field_simp [ne_of_gt ha.pos]
    <;> ring
  rw [hconst] at he
  have hn : ‖(u : BallH1)‖ = ‖u‖ := rfl
  rw [hn] at he
  simpa only [Pi.zero_def,pow_two,mul_assoc] using he

theorem isCoercive_unitBall_smallDrift
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {b : R3 → R3} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hb : AEStronglyMeasurable b ((volume : Measure R3).restrict ballOpens))
    (hbound : ∀ z ∈ (ballOpens : Set R3), ‖b z‖ ≤ lam/4)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (b z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) := by
  have hlam : 0 < lam := ha.pos
  refine ⟨3*lam/40,by positivity,?_⟩
  intro u
  rw [TauCeti.PDE.energyFormH1L0_apply]
  exact unitBall_smallDrift_coercivity ha hm hb hbound u

theorem norm_unitBall_smallDrift_functionalInverse_le
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {b : R3 → R3} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hb : AEStronglyMeasurable b ((volume : Measure R3).restrict ballOpens))
    (hbound : ∀ z ∈ (ballOpens : Set R3), ‖b z‖ ≤ lam/4)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (b z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤ 40/(3*lam) := by
  have hlam : 0 < lam := ha.pos
  have h := norm_functionalInverse_le (TauCeti.PDE.energyFormH1L0 hcoeff)
    (3*lam/40) (by positivity)
    (fun u => by
      rw [TauCeti.PDE.energyFormH1L0_apply]
      exact unitBall_smallDrift_coercivity ha hm hb hbound u)
  simpa only [inv_div] using h

theorem existsUnique_unitBall_smallDrift_weakSolution
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {b : R3 → R3} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hb : AEStronglyMeasurable b ((volume : Measure R3).restrict ballOpens))
    (hbound : ∀ z ∈ (ballOpens : Set R3), ‖b z‖ ≤ lam/4)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    ∃! u : BallH1Zero, TauCeti.PDE.IsWeakSolutionDirichlet a b 0 f u ∧
      ‖u‖ ≤ (40/(3*lam))*‖f‖ := by
  have hlam : 0 < lam := ha.pos
  let hcoeff := unitBall_smallDrift_energy_memLp ha hm hb hbound
  let hc := isCoercive_unitBall_smallDrift ha hm hb hbound hcoeff
  let u := TauCeti.PDE.weakSolutionDirichlet hcoeff hc f
  have hu : TauCeti.PDE.IsWeakSolutionDirichlet a b 0 f u :=
    TauCeti.PDE.isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hc f
  refine ⟨u,⟨hu,?_⟩,?_⟩
  · have h := TauCeti.PDE.norm_le_of_isWeakSolutionDirichlet
      (show 0 < 3*lam/40 by positivity)
      (fun v => by
        have hv := unitBall_smallDrift_coercivity ha hm hb hbound v
        simpa only [pow_two,mul_assoc] using hv) hu
    convert h using 1 <;> field_simp [ne_of_gt hlam] <;> ring
  · intro v hv
    exact TauCeti.PDE.eq_weakSolutionDirichlet hcoeff hc hv.1

theorem exists_uniform_smallRadius_drift_coercivity
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (q : Set R3) (eta lam Lam C : ℝ) (heta : 0 < eta) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hUE : ∀ p ∈ q ×ˢ Icc (-eta) eta, TauCeti.PDE.UniformlyEllipticOn
      (ballOpens : Set R3) (fun z => a (p,z)) lam Lam)
    (hbound : ∀ p ∈ q ×ˢ Icc (-eta) eta, ∀ z ∈ (ballOpens : Set R3), ‖b (p,z)‖ ≤ C*|p.2|) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      ∀ p ∈ q ×ˢ Icc (-delta) delta,
        (∀ z ∈ (ballOpens : Set R3), ‖b (p,z)‖ ≤ lam/4) ∧
        (3*lam/40 > 0) ∧
        (∀ u : BallH1Zero, (3*lam/40)*‖u‖*‖u‖ ≤
          TauCeti.PDE.energyFormH1 (fun z => a (p,z)) (fun z => b (p,z)) 0 (u : BallH1) (u : BallH1)) ∧
        (∃ hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a (p,z)) (b (p,z)) 0) ⊤
          ((volume : Measure R3).restrict ballOpens),
          IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) ∧
          ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤ 40/(3*lam)) ∧
        ∀ f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
          ∃! u : BallH1Zero, TauCeti.PDE.IsWeakSolutionDirichlet
            (fun z => a (p,z)) (fun z => b (p,z)) 0 f u ∧ ‖u‖ ≤ (40/(3*lam))*‖f‖ := by
  let delta := min eta (lam/(4*(C+1)))
  have hd : 0 < delta := lt_min heta (by positivity)
  refine ⟨delta,hd,min_le_left _ _,?_⟩
  intro p hp
  have hpE : p ∈ q ×ˢ Icc (-eta) eta :=
    ⟨hp.1,⟨by linarith [hp.2.1,min_le_left eta (lam/(4*(C+1)))],
      by linarith [hp.2.2,min_le_left eta (lam/(4*(C+1))) ]⟩⟩
  have hsmall (z : R3) (hz : z ∈ (ballOpens : Set R3)) : ‖b (p,z)‖ ≤ lam/4 := by
    calc
      _ ≤ C*|p.2| := hbound p hpE z hz
      _ ≤ (C+1)*|p.2| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (C+1)*(lam/(4*(C+1))) := mul_le_mul_of_nonneg_left
        ((abs_le.mpr hp.2).trans (min_le_right _ _)) (by positivity)
      _ = lam/4 := by field_simp [ne_of_gt (show 0 < C+1 by linarith)]
  have hm : AEStronglyMeasurable (fun z => a (p,z)) ((volume : Measure R3).restrict ballOpens) :=
    (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbm : AEStronglyMeasurable (fun z => b (p,z)) ((volume : Measure R3).restrict ballOpens) :=
    (hb.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  let hcoeff := unitBall_smallDrift_energy_memLp (hUE p hpE) hm hbm hsmall
  exact ⟨hsmall,by positivity,unitBall_smallDrift_coercivity (hUE p hpE) hm hbm hsmall,
    ⟨hcoeff,isCoercive_unitBall_smallDrift (hUE p hpE) hm hbm hsmall hcoeff,
      norm_unitBall_smallDrift_functionalInverse_le (hUE p hpE) hm hbm hsmall hcoeff⟩,
    existsUnique_unitBall_smallDrift_weakSolution (hUE p hpE) hm hbm hsmall⟩
end OAI.AnisotropicCalderon.DirichletFamily
