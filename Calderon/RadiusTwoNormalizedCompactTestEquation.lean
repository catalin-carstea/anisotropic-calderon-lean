import Calderon.RadiusTwoNativeEnergySourceRescaling
import Calderon.RadiusTwoUnitTestPushforward
import Calderon.RadiusTwoNativeSourceSolution
import Calderon.NativeZeroTestValueForcing

/-! EXPANSION.json precedes direct compact-test normalization of the actual source. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Distributions InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

run_cmd Lean.logInfo "BEFORE HEADER actual normalized compact-test equation"

theorem radiusTwoSourceSolution_dilated_compactTest_equation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (f : RadiusTwoL2)
    (φ : 𝓓(ballOpens, ℝ)) :
    TauCeti.PDE.energyFormH1 (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg f) : BallH1)
      (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 φ) =
      ∫ x in ballOpens, ((4 : ℝ) • radiusTwoNativeL2Dilation f) x * φ x
        ∂(volume : Measure R3) := by
  trace "PROOFENTER actual normalized compact-test equation"
  let g2 : MatrixField := enlargedBallNormalizedMetric g 2
  let w : RadiusTwoH1Zero := radiusTwoSourceSolution g hg f
  let u : BallH1Zero := radiusTwoNativeZeroDilation w
  let ψ : 𝓓(radiusTwoOpens, ℝ) := radiusTwoUnitTestPushforward φ
  let v : RadiusTwoH1Zero := nativeZeroTestLinear radiusTwoOpens ψ
  have hD : radiusTwoNativeZeroDilation v = nativeZeroTestLinear ballOpens φ :=
    (radiusTwoNativeZeroDilation_test ψ).trans
      (congrArg (fun τ : 𝓓(ballOpens, ℝ) => nativeZeroTestLinear ballOpens τ)
        (radiusTwoTestPullback_unitTestPushforward φ))
  have hE : TauCeti.PDE.energyFormH1 (principalCoefficient g2)
      (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1)
      (nativeZeroTestLinear ballOpens φ : BallH1) =
      4 * TauCeti.PDE.dirichletForcing (radiusTwoNativeL2Dilation f)
        (nativeZeroTestLinear ballOpens φ) := by
    calc
      _ = TauCeti.PDE.energyFormH1 (principalCoefficient g2)
          (0 : R3 → R3) (0 : R3 → ℝ)
          (radiusTwoNativeZeroDilation w : BallH1) (radiusTwoNativeZeroDilation v : BallH1) :=
        congrArg (fun z : BallH1Zero => TauCeti.PDE.energyFormH1 (principalCoefficient g2)
          (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1) (z : BallH1)) hD.symm
      _ = (1/2 : ℝ) * TauCeti.PDE.energyFormH1 (principalCoefficient g)
          (0 : R3 → R3) (0 : R3 → ℝ) (w : RadiusTwoH1) (v : RadiusTwoH1) :=
        nativeMetricEnergy_radiusTwo_rescaling g w v
      _ = (1/2 : ℝ) * TauCeti.PDE.dirichletForcing f v :=
        congrArg (fun r : ℝ => (1/2 : ℝ)*r) (radiusTwoSourceSolution_equation g hg f v)
      _ = (1/2 : ℝ) * (8 * TauCeti.PDE.dirichletForcing (radiusTwoNativeL2Dilation f)
          (radiusTwoNativeZeroDilation v)) :=
        congrArg (fun r : ℝ => (1/2 : ℝ)*r) (nativeDirichletForcing_radiusTwo_rescaling f v)
      _ = 4 * TauCeti.PDE.dirichletForcing (radiusTwoNativeL2Dilation f)
          (radiusTwoNativeZeroDilation v) := by ring
      _ = _ := congrArg (fun z : BallH1Zero =>
        4 * TauCeti.PDE.dirichletForcing (radiusTwoNativeL2Dilation f) z) hD
  have hPair : TauCeti.PDE.dirichletForcing (radiusTwoNativeL2Dilation f)
      (nativeZeroTestLinear ballOpens φ) =
      ∫ x in ballOpens, radiusTwoNativeL2Dilation f x * φ x ∂(volume : Measure R3) :=
    dirichletForcing_nativeZeroTest_eq_integral ballOpens (radiusTwoNativeL2Dilation f) φ
  have hDensity :
      (∫ x in ballOpens, ((4 : ℝ) • radiusTwoNativeL2Dilation f) x * φ x ∂(volume : Measure R3)) =
        4 * (∫ x in ballOpens, radiusTwoNativeL2Dilation f x * φ x ∂(volume : Measure R3)) :=
    integral_smul_Lp_mul_nativeTest ballOpens (4 : ℝ) (radiusTwoNativeL2Dilation f) φ
  have hNative :
      TauCeti.PDE.energyFormH1 (principalCoefficient g2) (0 : R3 → R3) (0 : R3 → ℝ)
        (u : BallH1) (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 φ) =
      TauCeti.PDE.energyFormH1 (principalCoefficient g2) (0 : R3 → R3) (0 : R3 → ℝ)
        (u : BallH1) (nativeZeroTestLinear ballOpens φ : BallH1) :=
    congrArg (fun z : BallH1 => TauCeti.PDE.energyFormH1 (principalCoefficient g2)
      (0 : R3 → R3) (0 : R3 → ℝ) (u : BallH1) z) (nativeZeroTestLinear_coe ballOpens φ).symm
  exact hNative.trans (hE.trans ((congrArg (fun r : ℝ => 4*r) hPair).trans hDensity.symm))


end OAI.AnisotropicCalderon.ExteriorSource
