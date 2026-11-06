import Calderon.ActualReferenceWeakDirichletEvaluation
import Calderon.CoerciveFunctionalInverseEquality

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem eq_sub_functionalInverse_of_restriction
    (R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (hA : IsCoercive A)
    (hrest : ∀ c v : BallH1Zero, A c v = R (c : BallH1) v)
    (E U : BallH1)
    (hz : E-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hRU : ∀ v : BallH1Zero, R U v = 0) :
    U = E-(functionalInverse A (R E) : BallH1) := by
  let c : BallH1Zero := ⟨E-U,hz⟩
  have hc : c = functionalInverse A (R E) := by
    apply eq_functionalInverse A hA (R E) c
    intro v
    have hsub : R (c : BallH1) v = R E v-R U v :=
      congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (map_sub R E U)
    have hscalar : R E v-R U v = R E v :=
      (congrArg (fun t : ℝ => R E v-t) (hRU v)).trans (sub_zero (R E v))
    exact (hrest c v).trans (hsub.trans hscalar)
  have hcv := congrArg (fun z : BallH1Zero => z.val) hc
  have hsolve : U = E-(c : BallH1) := by
    change U = E-(E-U)
    abel
  exact hsolve.trans (congrArg (fun V : BallH1 => E-V) hcv)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
