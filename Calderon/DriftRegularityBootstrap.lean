import Calderon.SupportedStrongOperatorEnergy
import Calderon.SupportedStrongOperatorInjective
import Calderon.SupportedStrongOperatorSurjective
import Calderon.SupportedDriftRegularity
import Calderon.BanachInverseFamily
import Calderon.CompactInverseDerivativeBounds

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

/-- Weak coercivity alone supplies pointwise strong invertibility at every Sobolev order. -/
theorem supportedStrongOperatorL_isInvertible
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (F : SmoothCoefficientMatrix (s + 2)) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s + 2) F) lam Lam)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0)
    (hsmall : ∀ z ∈ (ballOpens : Set R3), ‖beta z‖ ≤ lam / 4) :
    (supportedStrongOperatorL hcalc s F beta hbeta K hK hz).IsInvertible := by
  let a : R3 → Matrix (Fin 3) (Fin 3) ℝ := coefficientMatrixField (s + 2) F
  have hm : AEStronglyMeasurable a ((volume : Measure R3).restrict ballOpens) :=
    aestronglyMeasurable_coefficientMatrixField (s + 2) F
  have hbm : AEStronglyMeasurable beta ((volume : Measure R3).restrict ballOpens) :=
    hbeta.continuous.aestronglyMeasurable
  have hcoeff0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_coefficientMatrixEnergyIntegrand (s + 2) F hUE
  have hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) (beta z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
    unitBall_smallDrift_energy_memLp (a := a) (b := beta) (lam := lam) (Lam := Lam)
      hUE hm hbm hsmall
  have hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) (a := a) (b := beta) (c := (0 : R3 → ℝ)) hcoeff) :=
    isCoercive_unitBall_smallDrift (a := a) (b := beta) (lam := lam) (Lam := Lam)
      hUE hm hbm hsmall hcoeff
  let A : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
    supportedStrongOperatorL hcalc s F beta hbeta K hK hz
  have hinj : Function.Injective A :=
    supportedStrongOperatorL_injective_of_isCoercive
      (hcalc := hcalc) (s := s) (F := F) (hcoeff0 := hcoeff0)
      (beta := beta) (hbeta := hbeta) (K := K) (hK := hK) (hz := hz)
      (hcoeff := hcoeff) (hc := hc)
  obtain ⟨C, hC, hregular⟩ := exists_supportedDrift_regularity_bound
    (hcalc := hcalc) (hreg := hreg) (a := a) (lam := lam) (Lam := Lam)
    (hsmooth := contDiffOn_coefficientMatrixField_closedBall (s + 2) F)
    (hUE := hUE) (hcoeff := hcoeff0) (beta := beta) (hbeta := hbeta)
    (K := K) (hK := hK) (hz := hz) (s := s)
  have hsurj : Function.Surjective A :=
    supportedStrongOperatorL_surjective_of_regularity
      (hcalc := hcalc) (s := s) (F := F) (hcoeff0 := hcoeff0)
      (beta := beta) (hbeta := hbeta) (K := K) (hK := hK) (hz := hz)
      (hcoeff := hcoeff) (hc := hc) (C := C) (hregular := hregular)
  have hker : A.toLinearMap.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : A.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  exact ⟨ContinuousLinearEquiv.ofBijective A hker hrange,
    ContinuousLinearEquiv.coe_ofBijective A hker hrange⟩

/-- Every Sobolev inverse projects to exactly the pinned Tau weak solution. -/
theorem supportedStrongOperatorL_inverse_projection
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F : SmoothCoefficientMatrix (s + 2))
    (hcoeff0 : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField (s + 2) F z) (beta z) 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff))
    (hi : (supportedStrongOperatorL hcalc s F beta hbeta K hK hz).IsInvertible)
    (f : BallSobolev s) :
    strongDirichletProjectionL s
      ((supportedStrongOperatorL hcalc s F beta hbeta K hK hz).inverse f) =
        TauCeti.PDE.weakSolutionDirichlet hcoeff hc (TauCeti.Wkp.value s f) := by
  let A : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
    supportedStrongOperatorL hcalc s F beta hbeta K hK hz
  let U : StrongDirichletSpace s := A.inverse f
  let fDensity : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f
  let gDensity : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s (A U)
  have hAU : A U = f := hi.self_apply_inverse f
  have hDensity : gDensity = fDensity :=
    congrArg (fun Y : BallSobolev s =>
      TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) s Y) hAU
  let u : BallH1Zero := TauCeti.PDE.weakSolutionDirichlet
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := coefficientMatrixField (s + 2) F) (b := beta) (c := (0 : R3 → ℝ))
    hcoeff hc fDensity
  have hu : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
      (Omega := ballOpens) (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ) fDensity u :=
    TauCeti.PDE.isWeakSolutionDirichlet_weakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := coefficientMatrixField (s + 2) F) (b := beta) (c := (0 : R3 → ℝ))
      hcoeff hc fDensity
  have hEnergy : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
        (strongDirichletProjectionL s U : BallH1) (v : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ) (u : BallH1) (v : BallH1) := by
    intro v
    have hForcing : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
        (Omega := ballOpens) gDensity v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
        (Omega := ballOpens) fDensity v :=
      congrArg (fun g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
        TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3))
          (Omega := ballOpens) g v) hDensity
    exact (supportedStrongOperatorL_energy hcalc s F hcoeff0 beta hbeta K hK hz U v).symm.trans
      (hForcing.trans (hu v).symm)
  exact eq_of_unitBall_energyFormH1_eq
    (a := coefficientMatrixField (s + 2) F) (beta := beta) (hcoeff := hcoeff) (hc := hc)
    (u := strongDirichletProjectionL s U) (v := u) (h := hEnergy)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
