import Calderon.SupportedStrongOperatorEnergy
import Calderon.UnitBallEnergyUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem strongDirichletProjectionL_eq_of_supportedStrongOperatorL_eq
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F : SmoothCoefficientMatrix (s + 2))
    (hcoeff0 : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) (beta z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := coefficientMatrixField (s + 2) F)
      (b := beta) (c := (0 : R3 → ℝ)) hcoeff))
    (U V : StrongDirichletSpace s)
    (hUV : supportedStrongOperatorL hcalc s F beta hbeta K hK hz U =
      supportedStrongOperatorL hcalc s F beta hbeta K hK hz V) :
    strongDirichletProjectionL s U = strongDirichletProjectionL s V := by
  have hEnergy : ∀ w : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
        (strongDirichletProjectionL s U : BallH1) (w : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
        (strongDirichletProjectionL s V : BallH1) (w : BallH1) := by
    intro w
    have hForcing : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
        (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s (supportedStrongOperatorL hcalc s F beta hbeta K hK hz U)) w =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
        (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s (supportedStrongOperatorL hcalc s F beta hbeta K hK hz V)) w :=
      congrArg (fun Y : BallSobolev s =>
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
          (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
            (p := 2) s Y) w) hUV
    exact (supportedStrongOperatorL_energy hcalc s F hcoeff0 beta hbeta K hK hz U w).symm.trans
      (hForcing.trans (supportedStrongOperatorL_energy hcalc s F hcoeff0 beta hbeta K hK hz V w))
  exact eq_of_unitBall_energyFormH1_eq
    (a := coefficientMatrixField (s + 2) F) (beta := beta) (hcoeff := hcoeff) (hc := hc)
    (u := strongDirichletProjectionL s U) (v := strongDirichletProjectionL s V) (h := hEnergy)

theorem supportedStrongOperatorL_injective_of_isCoercive
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F : SmoothCoefficientMatrix (s + 2))
    (hcoeff0 : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) (beta z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := coefficientMatrixField (s + 2) F)
      (b := beta) (c := (0 : R3 → ℝ)) hcoeff)) :
    Function.Injective (supportedStrongOperatorL hcalc s F beta hbeta K hK hz) := by
  intro U V hUV
  apply strongDirichletProjectionL_injective s
  exact strongDirichletProjectionL_eq_of_supportedStrongOperatorL_eq
    (hcalc := hcalc) (s := s) (F := F) (hcoeff0 := hcoeff0)
    (beta := beta) (hbeta := hbeta) (K := K) (hK := hK) (hz := hz)
    (hcoeff := hcoeff) (hc := hc) (U := U) (V := V) (hUV := hUV)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
