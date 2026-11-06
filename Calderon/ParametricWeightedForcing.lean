import Calderon.ParametricCoerciveInverse
import Calderon.SmoothSobolevBridge
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

section GeneralForcing
variable {V H : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Bundle the real Hilbert pairing against one fixed value map before specialization. -/
def forcingFromValueL (j : V →L[ℝ] H) : H →L[ℝ] StrongDual ℝ V :=
  ((ContinuousLinearMap.compL ℝ V H ℝ).flip j).comp (innerSL ℝ)

theorem forcingFromValueL_apply (j : V →L[ℝ] H) (f : H) :
    forcingFromValueL j f = (innerSL ℝ f).comp j := rfl
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compose a forcing with a density product before specializing its carrier. -/
def composeWeightedForcingL (F : H →L[ℝ] StrongDual ℝ V)
    (M : W →L[ℝ] H →L[ℝ] H) : W →L[ℝ] H →L[ℝ] StrongDual ℝ V :=
  (ContinuousLinearMap.compL ℝ H H (StrongDual ℝ V) F).comp M

theorem composeWeightedForcingL_apply (F : H →L[ℝ] StrongDual ℝ V)
    (M : W →L[ℝ] H →L[ℝ] H) (w : W) (f : H) :
    composeWeightedForcingL F M w f = F (M w f) := rfl
end GeneralForcing

/-- Tau's actual Dirichlet value pairing, with its carrier inferred from valueL. -/
def unitBallDirichletForcingL :=
  forcingFromValueL (TauCeti.W1p0.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))

/-- The actual L-infinity by L2 scalar Holder product. -/
def unitBallWeightedLpL :
    Lp ℝ ⊤ ((volume : Measure R3).restrict ballOpens) →L[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL
    ((volume : Measure R3).restrict ballOpens) ⊤ 2 2

theorem unitBallWeightedLpL_ae
    (w : Lp ℝ ⊤ ((volume : Measure R3).restrict ballOpens))
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    unitBallWeightedLpL w f =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => w x * f x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder w f

theorem norm_unitBallWeightedLpL_apply_le
    (w : Lp ℝ ⊤ ((volume : Measure R3).restrict ballOpens))
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    ‖unitBallWeightedLpL w f‖ ≤ ‖w‖ * ‖f‖ := by
  change ‖(ContinuousLinearMap.mul ℝ ℝ).holder 2 w f‖ ≤ ‖w‖ * ‖f‖
  simpa only [ContinuousLinearMap.opNorm_mul, one_mul] using
    (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le w f

/-- The density-weighted forcing retains the factor w on the right-hand side. -/
def unitBallWeightedForcingL :=
  composeWeightedForcingL (V := BallH1Zero)
    (H := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (W := Lp ℝ ⊤ ((volume : Measure R3).restrict ballOpens))
    unitBallDirichletForcingL unitBallWeightedLpL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_unitBallWeightedForcing {n : WithTop ℕ∞}
    (w : E → Lp ℝ ⊤ ((volume : Measure R3).restrict ballOpens)) (s : Set E)
    (hw : ContDiffOn ℝ n w s) :
    ContDiffOn ℝ n (fun x => unitBallWeightedForcingL (w x)) s :=
  unitBallWeightedForcingL.contDiff.comp_contDiffOn hw


end OAI.AnisotropicCalderon.DirichletFamily
