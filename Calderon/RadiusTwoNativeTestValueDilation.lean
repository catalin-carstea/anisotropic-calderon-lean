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

theorem value_radiusTwoNativeZeroDilation_test (φ : 𝓓(radiusTwoOpens, ℝ)) :
    TauCeti.W1p.value (radiusTwoNativeZeroDilation
      (nativeZeroTestLinear radiusTwoOpens φ) : BallH1) =
        radiusTwoNativeL2Dilation (TauCeti.W1p.value
          (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1)) := by
  have hProjection (Ω : TopologicalSpace.Opens R3) (ψ : 𝓓(Ω, ℝ)) :
      TauCeti.W1p.value (nativeZeroTestLinear Ω ψ : TauCeti.W1p (volume : Measure R3) Ω 2) =
        TauCeti.testFunctionLp (mu := (volume : Measure R3)) 2 ψ := by
    rw [nativeZeroTestLinear_coe,TauCeti.W1p.value_ofTestFunctionₗ]
  have hLeft : TauCeti.W1p.value (radiusTwoNativeZeroDilation
      (nativeZeroTestLinear radiusTwoOpens φ) : BallH1) =
        TauCeti.testFunctionLp (mu := (volume : Measure R3)) 2 (radiusTwoTestPullback φ) :=
    (congrArg (fun z : BallH1Zero => TauCeti.W1p.value (z : BallH1))
      (radiusTwoNativeZeroDilation_test φ)).trans (hProjection ballOpens (radiusTwoTestPullback φ))
  have hRaw : TauCeti.testFunctionLp (mu := (volume : Measure R3)) 2 (radiusTwoTestPullback φ) =
      radiusTwoNativeL2Dilation (TauCeti.testFunctionLp (mu := (volume : Measure R3)) 2 φ) := by
    apply Lp.ext
    filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := volume) 2 (radiusTwoTestPullback φ),
      radiusTwoNativeL2Dilation_apply_ae (TauCeti.testFunctionLp (mu := (volume : Measure R3)) 2 φ),
      quasiMeasurePreserving_radiusTwo_comp_two.ae_eq_comp
        (TauCeti.testFunctionLp_apply_ae (mu := volume) 2 φ)] with x hL hR hOld
    exact hL.trans (hR.trans hOld).symm
  exact hLeft.trans (hRaw.trans
    (congrArg (radiusTwoNativeL2Dilation (V := ℝ)) (hProjection radiusTwoOpens φ)).symm)

end OAI.AnisotropicCalderon.ExteriorSource
