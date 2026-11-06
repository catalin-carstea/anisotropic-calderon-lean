import Calderon.SupportedDriftConsistency
import Calderon.BallEnergyRestriction

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

section PrincipalEquationElaboration



theorem dirichletForcing_sub_of_native_eq
    (f d e g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (v : BallH1Zero)
    (hf : g = f - d) (hd : d = e) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) g v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v -
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) e v := by
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
  have hProjected : P g = P f - P d :=
    (congrArg (fun x : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => P x) hf).trans
      (map_sub P f d)
  have hNative : P d = P e :=
    congrArg (fun x : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => P x) hd
  have hPairing : P g = P f - P e :=
    hProjected.trans (congrArg (fun t : ℝ => P f - t) hNative)
  exact (hP g).symm.trans
    (hPairing.trans (congrArg₂ (fun x y : ℝ => x - y) (hP f) (hP e)))


theorem principal_energy_eq_forcing_sub_of_native_eq
    (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (beta : R3 → R3)
    (F d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (w : BallH1) (v : BallH1Zero)
    (hsplit : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (0 : R3 → ℝ) w (v : BallH1) =
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          a (0 : R3 → R3) (0 : R3 → ℝ) w (v : BallH1) +
            TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v)
    (hweak : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (0 : R3 → ℝ) w (v : BallH1) =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) F v) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a (0 : R3 → R3) (0 : R3 → ℝ) w (v : BallH1) =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) F v -
          TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v := by
  let totalValue : ℝ :=
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (0 : R3 → ℝ) w (v : BallH1)
  let principalValue : ℝ :=
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a (0 : R3 → R3) (0 : R3 → ℝ) w (v : BallH1)
  let forcingValue : ℝ :=
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) F v
  let driftValue : ℝ :=
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v
  have hsplitScalar : totalValue = principalValue + driftValue := hsplit
  have hweakScalar : totalValue = forcingValue := hweak
  have hsumScalar : principalValue + driftValue = forcingValue :=
    @Eq.trans ℝ (principalValue + driftValue) totalValue forcingValue
      (@Eq.symm ℝ totalValue (principalValue + driftValue) hsplitScalar) hweakScalar
  have hsubtractScalar : principalValue = forcingValue - driftValue :=
    (eq_sub_iff_add_eq (a := principalValue) (b := forcingValue)
      (c := driftValue)).mpr hsumScalar
  exact hsubtractScalar


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Move only the lower-order drift to the forcing side at an order already available. -/
theorem principal_equation_of_supportedDrift_weakSolution (hcalc : FixedSobolevCalculus)
    (k : ℕ) (a : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (f : BallSobolev k) (u : BallH1Zero)
    (U : BallSobolev (k + 1)) (hU : TauCeti.Wkp.firstOrder k U = (u : BallH1))
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet a beta 0 (TauCeti.Wkp.value k f) u) :
    ∀ v : BallH1Zero, TauCeti.PDE.energyFormH1L0 hcoeff u v =
      TauCeti.PDE.dirichletForcing
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k
          ((f : BallSobolev k) -
            (supportedDriftL hcalc k beta hbeta K hK hz U : BallSobolev k))) v := by
  intro v
  have hsplit := energyFormH1_eq_principal_add_driftForcing hcalc a hcoeff
    beta hbeta K hK hz (u : BallH1) v
  have hD : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k (supportedDriftL hcalc k beta hbeta K hK hz U) =
      supportedDriftL hcalc 0 beta hbeta K hK hz (u : BallH1) :=
    (supportedDriftL_value_eq_firstOrder hcalc k beta hbeta K hK hz U).trans
      (congrArg (fun w : BallH1 => supportedDriftL hcalc 0 beta hbeta K hK hz w) hU)
  have hf : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k
      (f - supportedDriftL hcalc k beta hbeta K hK hz U) =
        TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k f - TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k
          (supportedDriftL hcalc k beta hbeta K hK hz U) :=
    map_sub (TauCeti.Wkp.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k) f _
  have hforcing : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) 
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k (f - supportedDriftL hcalc k beta hbeta K hK hz U)) v =
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)  (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k f) v -
          TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)  (supportedDriftL hcalc 0 beta hbeta K hK hz
            (u : BallH1)) v := by
    set_option backward.isDefEq.respectTransparency true in
      set_option backward.isDefEq.respectTransparency.types true in
        exact dirichletForcing_sub_of_native_eq
          (f := (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
            (p := 2) k f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)))
          (d := (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
            (p := 2) k (supportedDriftL hcalc k beta hbeta K hK hz U) :
              Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)))
          (e := (supportedDriftL hcalc 0 beta hbeta K hK hz (u : BallH1) :
            Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)))
          (g := (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
            (p := 2) k (f - supportedDriftL hcalc k beta hbeta K hK hz U) :
              Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)))
          (v := v) (hf := hf) (hd := hD)
  have hprincipal : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a 0 0 (u : BallH1) (v : BallH1) =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)  (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k f) v -
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)  (supportedDriftL hcalc 0 beta hbeta K hK hz
          (u : BallH1)) v := by
    set_option backward.isDefEq.respectTransparency true in
      set_option backward.isDefEq.respectTransparency.types true in
        exact principal_energy_eq_forcing_sub_of_native_eq
          (a := a) (beta := beta)
          (F := (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
            (p := 2) k f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)))
          (d := (supportedDriftL hcalc 0 beta hbeta K hK hz (u : BallH1) :
            Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)))
          (w := (u : BallH1)) (v := v) (hsplit := hsplit) (hweak := hu v)
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      have hfinal : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3))
          (Omega := ballOpens) a (0 : R3 → R3) (0 : R3 → ℝ)
          (u : BallH1) (v : BallH1) =
        TauCeti.PDE.dirichletForcing
          (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k
            (f - supportedDriftL hcalc k beta hbeta K hK hz U)) v :=
        hprincipal.trans hforcing.symm
      exact (energyFormH1L0_eq_energyFormH1_ball a hcoeff u v).trans hfinal


end PrincipalEquationElaboration

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
