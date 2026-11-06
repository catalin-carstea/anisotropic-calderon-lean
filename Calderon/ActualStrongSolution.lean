import Calderon.ActualWeakSolution
import Calderon.FixedDirichletRegularityData

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

variable (hreg : FixedDirichletRegularity) (s : ℕ)
  {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
  (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
  (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
  (hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens))
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
    ⊤ ((volume : Measure R3).restrict ballOpens))

/-- Select the actual regularity lift of the actual coercive weak solution. -/
def unitBallStrongSolution := fun f : BallSobolev s =>
  fixedStrongDirichletRegularityLift hreg s a lam Lam hsmooth ha hcoeff f
    (unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f))
    (fun v => unitBallWeakSolution_energy ha hm hcoeff (TauCeti.Wkp.value s f) v)

theorem unitBallStrongSolution_projection (f : BallSobolev s) :
    strongDirichletProjectionL s (unitBallStrongSolution hreg s hsmooth ha hm hcoeff f) =
      unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f) := by
  apply Subtype.ext
  exact (fixedDirichletRegularityLift_spec hreg s a lam Lam hsmooth ha hcoeff f
    (unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f))
    (fun v => unitBallWeakSolution_energy ha hm hcoeff (TauCeti.Wkp.value s f) v)).1

/-- One fixed strong-solution bound precedes every forcing input. -/
def unitBallStrongSolutionBound : ℝ :=
  fixedDirichletRegularityConstant hreg s a lam Lam hsmooth ha hcoeff * (5 / lam + 1)

theorem unitBallStrongSolutionBound_nonneg :
    0 ≤ unitBallStrongSolutionBound hreg s hsmooth ha hcoeff :=
  mul_nonneg (Classical.choose_spec (hreg s a lam Lam hsmooth ha hcoeff)).1
    (add_nonneg (div_nonneg (by norm_num) ha.pos.le) zero_le_one)

theorem norm_unitBallStrongSolution_le (f : BallSobolev s) :
    ‖unitBallStrongSolution hreg s hsmooth ha hm hcoeff f‖ ≤
      unitBallStrongSolutionBound hreg s hsmooth ha hcoeff * ‖f‖ := by
  have hC := (Classical.choose_spec (hreg s a lam Lam hsmooth ha hcoeff)).1
  have hw : ‖unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f)‖ ≤
      (5 / lam) * ‖f‖ :=
    (norm_unitBallWeakSolution_le ha hm hcoeff _).trans
      (mul_le_mul_of_nonneg_left (TauCeti.Wkp.norm_value_le s f)
        (div_nonneg (by norm_num) ha.pos.le))
  have hr := (fixedDirichletRegularityLift_spec hreg s a lam Lam hsmooth ha hcoeff f
    (unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f))
    (fun v => unitBallWeakSolution_energy ha hm hcoeff (TauCeti.Wkp.value s f) v)).2
  exact hr.trans (by
    change _ ≤ (fixedDirichletRegularityConstant hreg s a lam Lam hsmooth ha hcoeff *
      (5 / lam + 1)) * ‖f‖
    calc
      _ ≤ fixedDirichletRegularityConstant hreg s a lam Lam hsmooth ha hcoeff *
        ((5 / lam) * ‖f‖ + ‖f‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hw le_rfl) hC
      _ = _ := by ring)

theorem unitBallStrongSolution_add (f g : BallSobolev s) :
    unitBallStrongSolution hreg s hsmooth ha hm hcoeff (f + g) =
      unitBallStrongSolution hreg s hsmooth ha hm hcoeff f +
        unitBallStrongSolution hreg s hsmooth ha hm hcoeff g := by
  apply strongDirichletProjectionL_injective s
  calc
    strongDirichletProjectionL s
        (unitBallStrongSolution hreg s hsmooth ha hm hcoeff (f + g)) =
      unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s (f + g)) :=
        unitBallStrongSolution_projection hreg s hsmooth ha hm hcoeff _
    _ = unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f) +
        unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s g) :=
      (congrArg (unitBallWeakSolution ha hm hcoeff) (TauCeti.Wkp.value_add s f g)).trans
        (unitBallWeakSolution_add ha hm hcoeff _ _)
    _ = strongDirichletProjectionL s (unitBallStrongSolution hreg s hsmooth ha hm hcoeff f) +
        strongDirichletProjectionL s (unitBallStrongSolution hreg s hsmooth ha hm hcoeff g) :=
      congrArg₂ (fun x y : BallH1Zero => x + y)
        (unitBallStrongSolution_projection hreg s hsmooth ha hm hcoeff f).symm
        (unitBallStrongSolution_projection hreg s hsmooth ha hm hcoeff g).symm
    _ = _ := ((strongDirichletProjectionL s).map_add _ _).symm

theorem unitBallStrongSolution_smul (c : ℝ) (f : BallSobolev s) :
    unitBallStrongSolution hreg s hsmooth ha hm hcoeff (c • f) =
      c • unitBallStrongSolution hreg s hsmooth ha hm hcoeff f := by
  apply strongDirichletProjectionL_injective s
  calc
    strongDirichletProjectionL s
        (unitBallStrongSolution hreg s hsmooth ha hm hcoeff (c • f)) =
      unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s (c • f)) :=
        unitBallStrongSolution_projection hreg s hsmooth ha hm hcoeff _
    _ = c • unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f) :=
      (congrArg (unitBallWeakSolution ha hm hcoeff) (TauCeti.Wkp.value_smul s c f)).trans
        (unitBallWeakSolution_smul ha hm hcoeff c _)
    _ = c • strongDirichletProjectionL s
        (unitBallStrongSolution hreg s hsmooth ha hm hcoeff f) :=
      congrArg (fun x : BallH1Zero => c • x)
        (unitBallStrongSolution_projection hreg s hsmooth ha hm hcoeff f).symm
    _ = _ := ((strongDirichletProjectionL s).map_smul c _).symm

def unitBallStrongSolutionLinearMap : BallSobolev s →ₗ[ℝ] StrongDirichletSpace s where
  toFun := unitBallStrongSolution hreg s hsmooth ha hm hcoeff
  map_add' := unitBallStrongSolution_add hreg s hsmooth ha hm hcoeff
  map_smul' := unitBallStrongSolution_smul hreg s hsmooth ha hm hcoeff

def unitBallStrongSolutionL :=
  (unitBallStrongSolutionLinearMap hreg s hsmooth ha hm hcoeff).mkContinuous
    (unitBallStrongSolutionBound hreg s hsmooth ha hcoeff)
    (norm_unitBallStrongSolution_le hreg s hsmooth ha hm hcoeff)

theorem unitBallStrongSolutionL_apply (f : BallSobolev s) :
    unitBallStrongSolutionL hreg s hsmooth ha hm hcoeff f =
      unitBallStrongSolution hreg s hsmooth ha hm hcoeff f := rfl

theorem unitBallStrongSolutionL_energy (f : BallSobolev s) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 hcoeff
      (strongDirichletProjectionL s (unitBallStrongSolutionL hreg s hsmooth ha hm hcoeff f)) v =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
          (TauCeti.Wkp.value s f) v := by
  have hi : strongDirichletProjectionL s
      (unitBallStrongSolutionL hreg s hsmooth ha hm hcoeff f) =
      unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value s f) :=
    unitBallStrongSolution_projection hreg s hsmooth ha hm hcoeff f
  exact (congrArg (fun u : BallH1Zero => TauCeti.PDE.energyFormH1L0 hcoeff u v) hi).trans
    (unitBallWeakSolution_energy ha hm hcoeff _ v)

end OAI.AnisotropicCalderon.DirichletFamily
