import Calderon.NativeAllOrderFirstOrderSmoothValue
import Calderon.RadiusTwoNativeSmoothRepresentativeTransport

/-! EXPANSION.json precedes source-free actual all-order physical reconstruction. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoNativeZeroDilation

lemma exists_radiusTwoNativeAllOrder_innerBall_smooth_value
    (hcalc : FixedSobolevCalculus) (w : RadiusTwoH1Zero)
    (hLift : ∀ s : ℕ, ∃ U : BallSobolev (s+2),
      TauCeti.Wkp.firstOrder (s+1) U = (radiusTwoNativeZeroDilation w : BallH1))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (ball (0 : R3) (2*a)) ∧
      (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] G := by
  trace "PROOF ENTER source-free actual all-order physical reconstruction"
  let U : (s : ℕ) → BallSobolev (s+2) := fun s => Classical.choose (hLift s)
  have hU (s : ℕ) : TauCeti.Wkp.firstOrder (s+1) (U s) =
      (radiusTwoNativeZeroDilation w : BallH1) := Classical.choose_spec (hLift s)
  let b : ℝ := (a+1)/2
  have hb : 0 < b := by dsimp only [b]; linarith
  have hab : a < b := by dsimp only [b]; linarith
  have hb1 : b < 1 := by dsimp only [b]; linarith
  let u : BallH1 := (radiusTwoNativeZeroDilation w : BallH1)
  let P : (R3 → ℝ) → Prop := fun F =>
    Continuous F ∧ ContDiffOn ℝ ∞ F (ball (0 : R3) b) ∧
    (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) b)] F
  have hData : ∃ F : R3 → ℝ, P F :=
    exists_contDiffOn_innerBall_of_native_allOrder_firstOrder hcalc u U hU b hb hb1
  trace "SMOOTH PACKAGE MADE source-free actual all-order physical reconstruction"
  refine Exists.elim hData ?_
  intro F hF
  have hPhysical := radiusTwo_nativeNormalizedSmoothRepresentative_physical_transport
    w F a b ha hab hb1 hF.1 hF.2.1 hF.2.2
  exact ⟨(fun z : R3 => F ((1/2 : ℝ) • z)),hPhysical⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNativeAllOrder_innerBall_smooth_value
