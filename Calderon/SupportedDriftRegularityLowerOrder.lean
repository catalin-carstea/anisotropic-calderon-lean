import Calderon.SupportedDriftPrincipalRegularity

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

theorem isWeakSolutionDirichlet_lowerOrder
    (s : ℕ) (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (beta : R3 → R3)
    (f : BallSobolev (s + 1)) (u : BallH1Zero)
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
      (Omega := ballOpens) a beta (0 : R3 → ℝ)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (s + 1) f) u) :
    TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
      (Omega := ballOpens) a beta (0 : R3 → ℝ)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) s (TauCeti.Wkp.lowerOrder (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) s f)) u := by
  have hvalue :
      TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (s + 1) f =
      TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) s (TauCeti.Wkp.lowerOrder (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) s f) :=
    TauCeti.Wkp.value_succ (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) s f
  exact Eq.mp (congrArg
    (fun g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) =>
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
        (Omega := ballOpens) a beta (0 : R3 → ℝ) g u) hvalue) hu

theorem exists_supportedDrift_previous_order_lift
    (s : ℕ) (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (beta : R3 → R3)
    (B : ℝ) (hB : 0 ≤ B)
    (hprevious : ∀ (f : BallSobolev s) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
        (Omega := ballOpens) a beta (0 : R3 → ℝ)
        (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) s f) u →
      ∃ V : BallSobolev (s + 2),
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (s + 1) V = (u : BallH1) ∧
        ‖V‖ ≤ B * (‖u‖ + ‖f‖))
    (f : BallSobolev (s + 1)) (u : BallH1Zero)
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
      (Omega := ballOpens) a beta (0 : R3 → ℝ)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (s + 1) f) u) :
    ∃ V : BallSobolev (s + 2),
      TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) (s + 1) V = (u : BallH1) ∧
      ‖V‖ ≤ B * (‖u‖ + ‖f‖) := by
  let fLower : BallSobolev s :=
    TauCeti.Wkp.lowerOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) s f
  have huLower : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3))
      (Omega := ballOpens) a beta (0 : R3 → ℝ)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens)
        (p := 2) s fLower) u :=
    isWeakSolutionDirichlet_lowerOrder (s := s) (a := a) (beta := beta)
      (f := f) (u := u) (hu := hu)
  obtain ⟨V, hV, hVnorm⟩ := hprevious fLower u huLower
  have hLower : ‖fLower‖ ≤ ‖f‖ :=
    TauCeti.Wkp.norm_lowerOrder_le (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) s f
  have hSum : ‖u‖ + ‖fLower‖ ≤ ‖u‖ + ‖f‖ :=
    add_le_add (le_refl ‖u‖) hLower
  exact ⟨V, hV, hVnorm.trans (mul_le_mul_of_nonneg_left hSum hB)⟩


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
