import Calderon.SmoothSobolevBridge
import TauCeti.Analysis.Sobolev.Wkp.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

abbrev BallSobolev (k : ℕ) := TauCeti.Wkp (volume : Measure R3) ballOpens 2 k

theorem norm_unitBall_firstOrder_le (k : ℕ) (u : BallSobolev (k + 1)) :
    ‖TauCeti.Wkp.firstOrder k u‖ ≤ ‖u‖ := by
  induction k with
  | zero => simp only [TauCeti.Wkp.firstOrder_zero]; exact le_rfl
  | succ k ih =>
      rw [TauCeti.Wkp.firstOrder_succ]
      exact (ih _).trans (TauCeti.Wkp.norm_lowerOrder_le (k + 1) u)

/-- The closed strong domain imposes only the first-order Dirichlet condition. -/
def strongDirichletSubmodule (s : ℕ) : ClosedSubmodule ℝ (BallSobolev (s + 2)) :=
  (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).comap
    (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) (s + 1))

theorem mem_strongDirichletSubmodule (s : ℕ) (u : BallSobolev (s + 2)) :
    u ∈ strongDirichletSubmodule s ↔
      TauCeti.Wkp.firstOrder (s + 1) u ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
  Iff.rfl

abbrev StrongDirichletSpace (s : ℕ) := ↥(strongDirichletSubmodule s)

instance instCompleteSpaceStrongDirichletSpace (s : ℕ) :
    CompleteSpace (StrongDirichletSpace s) := inferInstance

/-- The actual first-order projection with its codomain restricted to W1p0. -/
def strongDirichletProjectionL (s : ℕ) :=
  ((TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) (s + 1)).comp (strongDirichletSubmodule s).toSubmodule.subtypeL).codRestrict
      (TauCeti.w1p0Submodule volume ballOpens 2).toSubmodule
      (fun u => u.2)

theorem strongDirichletProjectionL_apply (s : ℕ) (u : StrongDirichletSpace s) :
    (strongDirichletProjectionL s u : BallH1) =
      TauCeti.Wkp.firstOrder (s + 1) (u : BallSobolev (s + 2)) := rfl

theorem strongDirichletProjectionL_injective (s : ℕ) :
    Function.Injective (strongDirichletProjectionL s) := by
  intro u v h
  apply Subtype.ext
  apply TauCeti.Wkp.ext (s + 2)
  have hfirst := congrArg (fun z : BallH1Zero => (z : BallH1)) h
  change TauCeti.Wkp.firstOrder (s + 1) (u : BallSobolev (s + 2)) =
    TauCeti.Wkp.firstOrder (s + 1) (v : BallSobolev (s + 2)) at hfirst
  simpa only [TauCeti.Wkp.value_firstOrder] using congrArg TauCeti.W1p.value hfirst

theorem norm_strongDirichletProjectionL_apply_le (s : ℕ) (u : StrongDirichletSpace s) :
    ‖strongDirichletProjectionL s u‖ ≤ ‖u‖ :=
  norm_unitBall_firstOrder_le (s + 1) (u : BallSobolev (s + 2))

end OAI.AnisotropicCalderon.DirichletFamily
