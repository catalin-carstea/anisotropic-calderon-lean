import Calderon.StrongDirichletDomain
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Function
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-- The complete fixed-ball standard Sobolev calculus composite.
Relative results take this proposition explicitly. -/
def FixedSobolevCalculus : Prop :=
  (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ phi : R3 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
    ∀ M : ℝ, 0 ≤ M →
    (∀ j : ℕ, j ≤ k + 1 → ∀ x : R3, ‖iteratedFDeriv ℝ j phi x‖ ≤ M) →
    ∃ T : BallSobolev k →L[ℝ] BallSobolev k,
      (∀ f : BallSobolev k,
        TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k (T f)
          =ᵐ[((volume : Measure R3).restrict ballOpens)]
          fun x => phi x * TauCeti.Wkp.value (mu := (volume : Measure R3))
            (Omega := ballOpens) (p := 2) k f x) ∧ ‖T‖ ≤ C * M) ∧
  (∀ (k : ℕ) (i : Fin 3), ∃ D : BallSobolev (k + 1) →L[ℝ] BallSobolev k,
    ∀ u : BallSobolev (k + 1),
      TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k (D u)
        =ᵐ[((volume : Measure R3).restrict ballOpens)]
        fun x => (TauCeti.W1p.gradient (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) (TauCeti.Wkp.firstOrder k u) x) i)

end OAI.AnisotropicCalderon.DirichletFamily
