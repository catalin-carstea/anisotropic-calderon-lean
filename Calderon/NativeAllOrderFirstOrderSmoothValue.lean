import Calderon.NativeInteriorDirectSmoothReconstruction

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap

lemma exists_contDiffOn_innerBall_of_native_allOrder_firstOrder
    (hcalc : FixedSobolevCalculus) (u : BallH1)
    (U : (s : ℕ) → BallSobolev (s+2))
    (hU : ∀ s : ℕ, TauCeti.Wkp.firstOrder (s+1) (U s) = u)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (ball (0 : R3) a) ∧
      (TauCeti.W1p.value u : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] G := by
  have hV (s : ℕ) : TauCeti.Wkp.value (s+2) (U s) = TauCeti.W1p.value u :=
    (TauCeti.Wkp.value_firstOrder (s+1) (U s)).symm.trans
      (congrArg (fun w : BallH1 => TauCeti.W1p.value w) (hU s))
  have hValues : ∀ s : ℕ, TauCeti.Wkp.value (s+2) (U s) = TauCeti.Wkp.value 2 (U 0) :=
    fun s => (hV s).trans (hV 0).symm
  obtain ⟨G,hG,hSmooth,hAE⟩ :=
    exists_contDiffOn_infty_of_nativeAllOrderValues hcalc U hValues a ha ha1
  refine ⟨G,hG,hSmooth,?_⟩
  filter_upwards [hAE] with x hx
  exact (congrArg (fun v : BallSobolev 0 => (v : R3 → ℝ) x) (hV 0).symm).trans hx

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_contDiffOn_innerBall_of_native_allOrder_firstOrder
