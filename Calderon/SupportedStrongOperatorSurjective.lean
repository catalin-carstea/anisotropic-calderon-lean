import Calderon.SupportedStrongOperatorEnergy
import Calderon.DirichletForcingInjectivity

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

theorem supportedStrongOperatorL_surjective_of_regularity
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
    (C : ℝ)
    (hregular : ∀ (f : BallSobolev s) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
        (Omega := ballOpens) (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s f) u →
      ∃ U : BallSobolev (s + 2),
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (s + 1) U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f‖)) :
    Function.Surjective (supportedStrongOperatorL hcalc s F beta hbeta K hK hz) := by
  let A : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
    supportedStrongOperatorL hcalc s F beta hbeta K hK hz
  intro f
  let u : BallH1Zero := TauCeti.PDE.weakSolutionDirichlet
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := coefficientMatrixField (s + 2) F) (b := beta) (c := (0 : R3 → ℝ)) hcoeff hc
    (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f)
  have hu : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
      (Omega := ballOpens) (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f) u :=
    TauCeti.PDE.isWeakSolutionDirichlet_weakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := coefficientMatrixField (s + 2) F) (b := beta) (c := (0 : R3 → ℝ))
      hcoeff hc
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f)
  obtain ⟨U, hU, hUnorm⟩ := hregular f u hu
  have hBoundary : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) (s + 1) U ∈
        TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    Eq.mp (congrArg (fun w : BallH1 =>
      w ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) hU.symm) u.2
  let V : StrongDirichletSpace s :=
    ⟨U, (mem_strongDirichletSubmodule s U).mpr hBoundary⟩
  have hV : strongDirichletProjectionL s V = u := by
    apply Subtype.ext
    exact (strongDirichletProjectionL_apply s V).trans hU
  have hProjected : (strongDirichletProjectionL s V : BallH1) = (u : BallH1) :=
    congrArg (fun t : BallH1Zero => (t : BallH1)) hV
  have hForcing : ∀ w : BallH1Zero,
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s (A V)) w =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s f) w := by
    intro w
    have hEnergy : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3))
        (Omega := ballOpens) (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
        (strongDirichletProjectionL s V : BallH1) (w : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3))
        (Omega := ballOpens) (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ)
        (u : BallH1) (w : BallH1) :=
      congrArg (fun t : BallH1 => TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField (s + 2) F) beta (0 : R3 → ℝ) t (w : BallH1)) hProjected
    exact (supportedStrongOperatorL_energy hcalc s F hcoeff0 beta hbeta K hK hz V w).trans
      (hEnergy.trans (hu w))
  have hValue : TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) s (A V) =
    TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f :=
    unitBallDirichletForcing_eq_of_forall
      (f := TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) s (A V))
      (g := TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) s f) (h := hForcing)
  exact ⟨V, TauCeti.Wkp.ext (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) s (u := A V) (v := f) hValue⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
