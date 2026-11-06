import Calderon.StrongOperatorForcing
import Calderon.CoordinateFluxEnergy

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem strongCoefficientOperator_energy (hcalc : FixedSobolevCalculus)
    (s : ℕ) (F : SmoothCoefficientMatrix (s + 2)) (u : StrongDirichletSpace s)
    (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (strongDirichletOperator hcalc s F u)) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) (coefficientMatrixField (s + 2) F) 0 0
        (strongDirichletProjectionL s u : BallH1) (v : BallH1) := by
  exact (strongCoefficientOperator_forcing_sum hcalc s F u v).trans
    (energyFormH1_eq_sum_coordinateFlux_inner
      (coefficientMatrixField (s + 2) F)
      (strongDirichletProjectionL s u : BallH1) (v : BallH1)
      (fun i j => TauCeti.Wkp.value (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) (s + 1)
          (coefficientMultiplier hcalc (s + 1) (F i j)
            (strongCoordinateDerivativeL hcalc s j u)))
      (fun i j => strongCoefficientFlux_value_ae hcalc s F i j u)).symm


theorem strongCoefficientOperator_energyL0 (hcalc : FixedSobolevCalculus)
    (s : ℕ) (F : SmoothCoefficientMatrix (s + 2))
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (u : StrongDirichletSpace s) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens) hcoeff (strongDirichletProjectionL s u) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (strongDirichletOperator hcalc s F u)) v := by
  exact (TauCeti.PDE.energyFormH1L0_apply hcoeff _ _).trans
    (strongCoefficientOperator_energy hcalc s F u v).symm

end OAI.AnisotropicCalderon.DirichletFamily
