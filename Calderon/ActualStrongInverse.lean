import Calderon.StrongOperatorEnergy
import Calderon.ActualStrongSolution
import Calderon.DirichletForcingInjectivity

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

def strongDirichletSolutionL (hreg : FixedDirichletRegularity) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) {lam Lam : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ (coefficientMatrixField (s + 2) F) (Metric.closedBall 0 2))
    (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s + 2) F) lam Lam)
    (hm : AEStronglyMeasurable (coefficientMatrixField (s + 2) F)
      ((volume : Measure R3).restrict ballOpens))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    BallSobolev s →L[ℝ] StrongDirichletSpace s :=
  unitBallStrongSolutionL hreg s hsmooth ha hm hcoeff

variable (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
  (F : SmoothCoefficientMatrix (s + 2)) {lam Lam : ℝ}
  (hsmooth : ContDiffOn ℝ ∞ (coefficientMatrixField (s + 2) F) (Metric.closedBall 0 2))
  (ha : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
    (coefficientMatrixField (s + 2) F) lam Lam)
  (hm : AEStronglyMeasurable (coefficientMatrixField (s + 2) F)
    ((volume : Measure R3).restrict ballOpens))
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
    (coefficientMatrixField (s + 2) F x) 0 0) ⊤
    ((volume : Measure R3).restrict ballOpens))

include hreg hsmooth ha hm hcoeff

theorem strongDirichletSolution_operator (u : StrongDirichletSpace s) :
    strongDirichletSolutionL hreg s F hsmooth ha hm hcoeff
      (strongDirichletOperator hcalc s F u) = u := by
  apply strongDirichletProjectionL_injective s
  have hp : strongDirichletProjectionL s u =
      unitBallWeakSolution ha hm hcoeff (TauCeti.Wkp.value
        (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
          (strongDirichletOperator hcalc s F u)) := by
    apply TauCeti.PDE.eq_weakSolutionDirichlet hcoeff
      (isCoercive_unitBall_zeroDrift ha hm hcoeff)
    intro v
    exact (strongCoefficientOperator_energy hcalc s F u v).symm
  exact (unitBallStrongSolution_projection hreg s hsmooth ha hm hcoeff
    (strongDirichletOperator hcalc s F u)).trans hp.symm

theorem strongDirichletOperator_solution (f : BallSobolev s) :
    strongDirichletOperator hcalc s F
      (strongDirichletSolutionL hreg s F hsmooth ha hm hcoeff f) = f := by
  apply TauCeti.Wkp.ext s
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  exact (strongCoefficientOperator_energyL0 hcalc s F hcoeff
    (strongDirichletSolutionL hreg s F hsmooth ha hm hcoeff f) v).symm.trans
      (unitBallStrongSolutionL_energy hreg s hsmooth ha hm hcoeff f v)

theorem strongDirichletSolution_comp_operator :
    (strongDirichletSolutionL hreg s F hsmooth ha hm hcoeff).comp
      (strongDirichletOperator hcalc s F) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro u
  exact strongDirichletSolution_operator hcalc hreg s F hsmooth ha hm hcoeff u

theorem strongDirichletOperator_comp_solution :
    (strongDirichletOperator hcalc s F).comp
      (strongDirichletSolutionL hreg s F hsmooth ha hm hcoeff) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  exact strongDirichletOperator_solution hcalc hreg s F hsmooth ha hm hcoeff f

theorem strongDirichletOperator_isInvertible : (strongDirichletOperator hcalc s F).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (strongDirichletOperator_comp_solution hcalc hreg s F hsmooth ha hm hcoeff)
    (strongDirichletSolution_comp_operator hcalc hreg s F hsmooth ha hm hcoeff)

theorem strongDirichletOperator_inverse_eq :
    (strongDirichletOperator hcalc s F).inverse =
      strongDirichletSolutionL hreg s F hsmooth ha hm hcoeff :=
  ContinuousLinearMap.inverse_eq
    (strongDirichletOperator_comp_solution hcalc hreg s F hsmooth ha hm hcoeff)
    (strongDirichletSolution_comp_operator hcalc hreg s F hsmooth ha hm hcoeff)

theorem norm_strongDirichletOperator_inverse_le :
    ‖(strongDirichletOperator hcalc s F).inverse‖ ≤
      unitBallStrongSolutionBound hreg s hsmooth ha hcoeff := by
  rw [strongDirichletOperator_inverse_eq hcalc hreg s F hsmooth ha hm hcoeff]
  apply ContinuousLinearMap.opNorm_le_bound _
    (unitBallStrongSolutionBound_nonneg hreg s hsmooth ha hcoeff)
  intro f
  exact norm_unitBallStrongSolution_le hreg s hsmooth ha hm hcoeff f

end OAI.AnisotropicCalderon.DirichletFamily
