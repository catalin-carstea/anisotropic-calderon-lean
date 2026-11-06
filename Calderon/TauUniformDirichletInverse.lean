import Calderon.ParametricCoerciveInverse
import Calderon.SmoothSobolevBridge

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem uniformlyEllipticOn_weightedCoefficient
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {w : R3 → ℝ}
    {s : Set R3} {lam Lam wm wM : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn s a lam Lam)
    (hm : 0 < wm) (hmM : wm ≤ wM)
    (hw : ∀ x ∈ s, wm ≤ w x ∧ w x ≤ wM) :
    TauCeti.PDE.UniformlyEllipticOn s (fun x => w x • a x)
      (wm * lam) (wM * Lam) := by
  refine ⟨mul_pos hm ha.pos, ?_, ?_⟩
  · exact mul_le_mul hmM ha.le ha.pos.le (hm.le.trans hmM)
  · intro x hx
    have hw0 : 0 ≤ w x := hm.le.trans (hw x hx).1
    have hquad (v : R3) : 0 ≤ (a x).toQuadraticForm' v :=
      (mul_nonneg ha.pos.le (sq_nonneg ‖v‖)).trans (ha.lower_bound hx v)
    constructor
    · intro v
      calc
        (wm * lam) * ‖v‖ ^ 2 = wm * (lam * ‖v‖ ^ 2) := by ring
        _ ≤ wm * (a x).toQuadraticForm' v :=
          mul_le_mul_of_nonneg_left (ha.lower_bound hx v) hm.le
        _ ≤ w x * (a x).toQuadraticForm' v :=
          mul_le_mul_of_nonneg_right (hw x hx).1 (hquad v)
        _ = (w x • a x).toQuadraticForm' v := by
          simp [Matrix.toQuadraticForm'_apply, smul_eq_mul]
    · intro eta xi
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_nonneg hw0]
      calc
        w x * |dotProduct eta (Matrix.mulVec (a x) xi)| ≤
            w x * (Lam * ‖eta‖ * ‖xi‖) :=
          mul_le_mul_of_nonneg_left (ha.upper_bound hx eta xi) hw0
        _ ≤ wM * (Lam * ‖eta‖ * ‖xi‖) :=
          mul_le_mul_of_nonneg_right (hw x hx).2
            (mul_nonneg (mul_nonneg ha.upper_nonneg (norm_nonneg eta)) (norm_nonneg xi))
        _ = (wM * Lam) * ‖eta‖ * ‖xi‖ := by ring

theorem memLp_zeroDriftEnergyIntegrand
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens)) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens) :=
  TauCeti.PDE.memLp_energyIntegrand_of_bounds ha.upper_nonneg hm
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ hx => ha.upper_bound hx)
    (beta := 0) (gamma := 0) (fun _ _ => by simp) (fun _ _ => by simp)

theorem unitBall_zeroDrift_coercivity
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens)) (u : BallH1Zero) :
    (lam / 5) * ‖u‖ * ‖u‖ ≤ TauCeti.PDE.energyFormH1L0 hcoeff u u := by
  have hp := TauCeti.W1p.norm_value_le_mul_norm_gradient_of_subset_ball
    (Omega := ballOpens) (c := (0 : R3)) (R := 1)
    (by decide : (2 : ℝ≥0∞) ≠ ⊤)
    (show (ballOpens : Set R3) ⊆ Metric.ball 0 1 from Set.Subset.rfl) u.2
  have he := ha.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift hm
    aestronglyMeasurable_const (b := (fun _ : R3 => (0 : R3)))
    (c := (fun _ : R3 => (0 : ℝ)))
    (gamma := 0) (P := 2) (fun _ _ => rfl) (fun _ _ => by simp)
    (fun _ _ => le_rfl) (u := (u : BallH1)) (by simpa using hp)
  rw [TauCeti.PDE.energyFormH1L0_apply]
  have hn : ‖(u : BallH1)‖ = ‖u‖ := rfl
  rw [hn] at he
  norm_num only [pow_two, show (2 : ℝ) * 2 + 1 = 5 by norm_num] at he
  simpa only [mul_assoc] using he

theorem isCoercive_unitBall_zeroDrift
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens)) :
    IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) :=
  ⟨lam / 5, div_pos ha.pos (by norm_num), unitBall_zeroDrift_coercivity ha hm hcoeff⟩

theorem norm_unitBall_functionalInverse_le
    {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens)) :
    ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤ 5 / lam := by
  simpa only [inv_div, one_div] using
    norm_functionalInverse_le (TauCeti.PDE.energyFormH1L0 hcoeff)
      (lam / 5) (div_pos ha.pos (by norm_num))
      (unitBall_zeroDrift_coercivity ha hm hcoeff)

theorem uniform_norm_unitBall_functionalInverse_le
    {X : Type*} (a : X → R3 → Matrix (Fin 3) (Fin 3) ℝ) (s : Set X)
    (lam Lam : ℝ)
    (hcoeff : ∀ x, MemLp (fun z => TauCeti.PDE.energyIntegrand (a x z) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens))
    (ha : ∀ x ∈ s, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (a x) lam Lam)
    (hm : ∀ x ∈ s, AEStronglyMeasurable (a x) ((volume : Measure R3).restrict ballOpens)) :
    ∀ x ∈ s, ‖functionalInverse (TauCeti.PDE.energyFormH1L0 (hcoeff x))‖ ≤ 5 / lam := by
  intro x hx
  exact norm_unitBall_functionalInverse_le (ha x hx) (hm x hx) (hcoeff x)

end OAI.AnisotropicCalderon.DirichletFamily
