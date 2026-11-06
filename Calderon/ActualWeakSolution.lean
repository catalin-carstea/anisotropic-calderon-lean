import Calderon.TauUniformDirichletInverse

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

variable {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
  (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
  (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
    ⊤ ((volume : Measure R3).restrict ballOpens))

/-- The actual pinned Tau Ceti weak solution with the ball coercivity proof. -/
def unitBallWeakSolution (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :=
  TauCeti.PDE.weakSolutionDirichlet hcoeff (isCoercive_unitBall_zeroDrift ha hm hcoeff) f

theorem unitBallWeakSolution_isWeakSolution
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    TauCeti.PDE.IsWeakSolutionDirichlet a 0 0 f (unitBallWeakSolution ha hm hcoeff f) :=
  TauCeti.PDE.isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff
    (isCoercive_unitBall_zeroDrift ha hm hcoeff) f

theorem unitBallWeakSolution_energy
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 hcoeff (unitBallWeakSolution ha hm hcoeff f) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v := by
  rw [TauCeti.PDE.energyFormH1L0_apply]
  exact unitBallWeakSolution_isWeakSolution ha hm hcoeff f v

theorem norm_unitBallWeakSolution_le
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    ‖unitBallWeakSolution ha hm hcoeff f‖ ≤ (5 / lam) * ‖f‖ := by
  have hb := TauCeti.PDE.norm_le_of_isWeakSolutionDirichlet
    (div_pos ha.pos (by norm_num : (0 : ℝ) < 5))
    (fun w => by
      change (lam / 5) * ‖w‖ ^ 2 ≤
        TauCeti.PDE.energyFormH1 a (fun _ => 0) (fun _ => 0) (w : BallH1) (w : BallH1)
      have hw := unitBall_zeroDrift_coercivity ha hm hcoeff w
      rw [TauCeti.PDE.energyFormH1L0_apply hcoeff] at hw
      simpa only [pow_two, mul_assoc] using hw)
    (unitBallWeakSolution_isWeakSolution ha hm hcoeff f)
  convert hb using 1 <;> field_simp

theorem unitBallWeakSolution_add
    (f g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    unitBallWeakSolution ha hm hcoeff (f + g) =
      unitBallWeakSolution ha hm hcoeff f + unitBallWeakSolution ha hm hcoeff g := by
  symm
  apply TauCeti.PDE.eq_weakSolutionDirichlet hcoeff (isCoercive_unitBall_zeroDrift ha hm hcoeff)
  intro v
  have hB := congrArg (fun ell => ell v)
    ((TauCeti.PDE.energyFormH1L0 hcoeff).map_add
      (unitBallWeakSolution ha hm hcoeff f) (unitBallWeakSolution ha hm hcoeff g))
  have h := hB.trans (congrArg₂ (fun x y : ℝ => x + y)
    (unitBallWeakSolution_energy ha hm hcoeff f v)
    (unitBallWeakSolution_energy ha hm hcoeff g v))
  rw [TauCeti.PDE.energyFormH1L0_apply] at h
  exact h.trans (by simp only [TauCeti.PDE.dirichletForcing_apply, inner_add_left])

theorem unitBallWeakSolution_smul (c : ℝ)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    unitBallWeakSolution ha hm hcoeff (c • f) = c • unitBallWeakSolution ha hm hcoeff f := by
  symm
  apply TauCeti.PDE.eq_weakSolutionDirichlet hcoeff (isCoercive_unitBall_zeroDrift ha hm hcoeff)
  intro v
  have hB := congrArg (fun ell => ell v)
    ((TauCeti.PDE.energyFormH1L0 hcoeff).map_smul c (unitBallWeakSolution ha hm hcoeff f))
  have h := hB.trans (congrArg (fun x : ℝ => c • x)
    (unitBallWeakSolution_energy ha hm hcoeff f v))
  rw [TauCeti.PDE.energyFormH1L0_apply] at h
  exact h.trans (by simp only [TauCeti.PDE.dirichletForcing_apply, inner_smul_left,
    conj_trivial, smul_eq_mul])

/-- The actual weak solution is linear by checked coercive uniqueness. -/
def unitBallWeakSolutionLinearMap :
    Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →ₗ[ℝ] BallH1Zero where
  toFun := unitBallWeakSolution ha hm hcoeff
  map_add' := unitBallWeakSolution_add ha hm hcoeff
  map_smul' := unitBallWeakSolution_smul ha hm hcoeff

/-- Its fixed bound is selected before the forcing data. -/
def unitBallWeakSolutionL :=
  (unitBallWeakSolutionLinearMap ha hm hcoeff).mkContinuous (5 / lam)
    (norm_unitBallWeakSolution_le ha hm hcoeff)

theorem unitBallWeakSolutionL_apply
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    unitBallWeakSolutionL ha hm hcoeff f = unitBallWeakSolution ha hm hcoeff f := rfl

end OAI.AnisotropicCalderon.DirichletFamily
