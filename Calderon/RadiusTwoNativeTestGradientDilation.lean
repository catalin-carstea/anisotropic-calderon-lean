import Calderon.RadiusTwoNativeL2Dilation

/-! EXPANSION.json precedes projection of the checked test-dilation equality. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal Distributions Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem gradient_radiusTwoNativeZeroDilation_test (φ : 𝓓(radiusTwoOpens, ℝ)) :
    TauCeti.W1p.gradient (radiusTwoNativeZeroDilation
      (nativeZeroTestLinear radiusTwoOpens φ) : BallH1) =
        (2 : ℝ) • radiusTwoNativeL2Dilation (TauCeti.W1p.gradient
          (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) := by
  have hProjection (Ω : TopologicalSpace.Opens R3) (ψ : 𝓓(Ω, ℝ)) :
      TauCeti.W1p.gradient (nativeZeroTestLinear Ω ψ : TauCeti.W1p (volume : Measure R3) Ω 2) =
        TauCeti.gradientTestFunctionLp (mu := (volume : Measure R3)) 2 ψ := by
    rw [nativeZeroTestLinear_coe,TauCeti.W1p.gradient_ofTestFunctionₗ]
  have hLeft : TauCeti.W1p.gradient (radiusTwoNativeZeroDilation
      (nativeZeroTestLinear radiusTwoOpens φ) : BallH1) =
        TauCeti.gradientTestFunctionLp (mu := (volume : Measure R3)) 2 (radiusTwoTestPullback φ) :=
    (congrArg (fun z : BallH1Zero => TauCeti.W1p.gradient (z : BallH1))
      (radiusTwoNativeZeroDilation_test φ)).trans (hProjection ballOpens (radiusTwoTestPullback φ))
  have hRaw : TauCeti.gradientTestFunctionLp (mu := (volume : Measure R3)) 2 (radiusTwoTestPullback φ) =
      (2 : ℝ) • radiusTwoNativeL2Dilation
        (TauCeti.gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ) := by
    apply Lp.ext
    filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 (radiusTwoTestPullback φ),
      Lp.coeFn_smul (2 : ℝ) (radiusTwoNativeL2Dilation
        (TauCeti.gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ)),
      radiusTwoNativeL2Dilation_apply_ae
        (TauCeti.gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ),
      quasiMeasurePreserving_radiusTwo_comp_two.ae_eq_comp
        (TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ)] with x hL hSmul hR hOld
    have hChain : gradient (radiusTwoTestPullback φ : R3 → ℝ) x =
        (2 : ℝ) • gradient (φ : R3 → ℝ) ((2 : ℝ) • x) :=
      gradient_comp_const_smul (φ : R3 → ℝ) 2 x
        (φ.contDiff.differentiable (by simp) ((2 : ℝ) • x))
    have hR' : ((2 : ℝ) • radiusTwoNativeL2Dilation
        (TauCeti.gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ)) x =
        (2 : ℝ) • gradient (φ : R3 → ℝ) ((2 : ℝ) • x) := by
      simpa only [Pi.smul_apply,Function.comp_apply] using hSmul.trans
        (congrArg (fun z : R3 => (2 : ℝ) • z) (hR.trans hOld))
    exact (hL.trans hChain).trans hR'.symm
  exact hLeft.trans (hRaw.trans
    (congrArg (fun z : Lp R3 2 ((volume : Measure R3).restrict radiusTwoOpens) =>
      (2 : ℝ) • radiusTwoNativeL2Dilation z) (hProjection radiusTwoOpens φ)).symm)

end OAI.AnisotropicCalderon.ExteriorSource
