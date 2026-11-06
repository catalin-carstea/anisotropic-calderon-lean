import Calderon.SupportedDriftConsistency
import Calderon.StrongOperatorEnergy

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

theorem dirichletForcing_add_of_native_eq
    (f d g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (v : BallH1Zero)
    (hg : g = f + d) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) g v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v +
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v := by
  let valueV : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.W1p.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
      (v : BallH1)
  let P : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ] ℝ :=
    innerSL ℝ valueV
  have hP (x : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
      P x = TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
        (Omega := ballOpens) x v :=
    (innerSL_apply_apply ℝ valueV x).trans ((real_inner_comm x valueV).trans
      (TauCeti.PDE.dirichletForcing_apply (mu := (volume : Measure R3))
        (Omega := ballOpens) x v).symm)
  have hProjected : P g = P f + P d :=
    (congrArg (fun x : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => P x) hg).trans
      (map_add P f d)
  exact (hP g).symm.trans
    (hProjected.trans (congrArg₂ (fun x y : ℝ => x + y) (hP f) (hP d)))

def supportedStrongOperatorL (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (beta : R3 → R3)
    (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  strongDirichletOperator hcalc s F + supportedStrongDriftL hcalc s beta hbeta K hK hz

theorem supportedStrongOperatorL_energy (hcalc : FixedSobolevCalculus) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2))
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (U : StrongDirichletSpace s) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (supportedStrongOperatorL hcalc s F beta hbeta K hK hz U)) v =
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          (coefficientMatrixField (s + 2) F) beta 0
          (strongDirichletProjectionL s U : BallH1) (v : BallH1) := by
  let u : BallH1 := (strongDirichletProjectionL s U : BallH1)
  let f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (strongDirichletOperator hcalc s F U)
  let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    supportedDriftL hcalc 0 beta hbeta K hK hz u
  have hOp : supportedStrongOperatorL hcalc s F beta hbeta K hK hz U =
      strongDirichletOperator hcalc s F U + supportedStrongDriftL hcalc s beta hbeta K hK hz U := rfl
  have hValue : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (supportedStrongOperatorL hcalc s F beta hbeta K hK hz U) = f + d :=
    (congrArg (fun V : BallSobolev s =>
      TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s V) hOp).trans
      ((TauCeti.Wkp.value_add (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
        (strongDirichletOperator hcalc s F U) (supportedStrongDriftL hcalc s beta hbeta K hK hz U)).trans
          (congrArg (fun x : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => f + x)
            (supportedStrongDriftL_value_eq hcalc s beta hbeta K hK hz U)))
  have hForcing := dirichletForcing_add_of_native_eq f d
    (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (supportedStrongOperatorL hcalc s F beta hbeta K hK hz U)) v hValue
  have hPrincipal : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
      (Omega := ballOpens) f v =
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          (coefficientMatrixField (s + 2) F) (0 : R3 → R3) (0 : R3 → ℝ) u (v : BallH1) :=
    strongCoefficientOperator_energy hcalc s F U v
  have hSplit : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ) u (v : BallH1) =
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          (coefficientMatrixField (s + 2) F) (0 : R3 → R3) (0 : R3 → ℝ) u (v : BallH1) +
            TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v :=
    energyFormH1_eq_principal_add_driftForcing hcalc
      (coefficientMatrixField (s + 2) F) hcoeff beta hbeta K hK hz u v
  exact hForcing.trans
    ((congrArg (fun x : ℝ => x + TauCeti.PDE.dirichletForcing
      (mu := (volume : Measure R3)) (Omega := ballOpens) d v) hPrincipal).trans hSplit.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
