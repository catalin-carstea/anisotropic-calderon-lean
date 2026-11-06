import Calderon.RadiusTwoNativeDilationJets
import Calderon.NativePrincipalEnergyGradientForm
import Calderon.RadiusTwoRescalingScalarTransport

/-! EXPANSION.json precedes the original exact native energy/source rescaling. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem nativeMetricEnergy_radiusTwo_rescaling (g : MatrixField) (w v : RadiusTwoH1Zero) :
    TauCeti.PDE.energyFormH1 (principalCoefficient (enlargedBallNormalizedMetric g 2))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (radiusTwoNativeZeroDilation w : BallH1) (radiusTwoNativeZeroDilation v : BallH1) =
    (1/2 : ℝ) * TauCeti.PDE.energyFormH1 (principalCoefficient g)
      (0 : R3 → R3) (0 : R3 → ℝ) (w : RadiusTwoH1) (v : RadiusTwoH1) := by
  have hGrad (u : RadiusTwoH1Zero) :
      (TauCeti.W1p.gradient (radiusTwoNativeZeroDilation u : BallH1) : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict ballOpens]
          (fun x : R3 => (2 : ℝ) • TauCeti.W1p.gradient (u : RadiusTwoH1) ((2 : ℝ) • x)) := by
    filter_upwards [Lp.coeFn_smul (2 : ℝ)
      (radiusTwoNativeL2Dilation (TauCeti.W1p.gradient (u : RadiusTwoH1))),
      radiusTwoNativeL2Dilation_apply_ae (TauCeti.W1p.gradient (u : RadiusTwoH1))] with x hs hp
    have he := congrArg (fun q : Lp R3 2 ((volume : Measure R3).restrict ballOpens) => q x)
      (gradient_radiusTwoNativeZeroDilation u)
    exact he.trans (hs.trans (congrArg (fun z : R3 => (2 : ℝ) • z) hp))
  have hInt := setIntegral_matrixBilinear_radiusTwo_transport
    (principalCoefficient g) (principalCoefficient (enlargedBallNormalizedMetric g 2))
    (TauCeti.W1p.gradient (v : RadiusTwoH1)) (TauCeti.W1p.gradient (w : RadiusTwoH1))
    (TauCeti.W1p.gradient (radiusTwoNativeZeroDilation v : BallH1))
    (TauCeti.W1p.gradient (radiusTwoNativeZeroDilation w : BallH1))
    (fun x => principalCoefficient_enlargedBallNormalizedMetric g 2 x) (hGrad v) (hGrad w)
  calc
    _ = ∫ x in ballOpens, TauCeti.PDE.matrixBilinearForm
        (principalCoefficient (enlargedBallNormalizedMetric g 2) x)
        (TauCeti.W1p.gradient (radiusTwoNativeZeroDilation v : BallH1) x)
        (TauCeti.W1p.gradient (radiusTwoNativeZeroDilation w : BallH1) x)
          ∂(volume : Measure R3) :=
      nativePrincipalEnergy_eq_gradient_setIntegral ballOpens
        (principalCoefficient (enlargedBallNormalizedMetric g 2))
        (radiusTwoNativeZeroDilation w : BallH1) (radiusTwoNativeZeroDilation v : BallH1)
    _ = (1/2 : ℝ) * (∫ z in radiusTwoOpens, TauCeti.PDE.matrixBilinearForm (principalCoefficient g z)
        (TauCeti.W1p.gradient (v : RadiusTwoH1) z) (TauCeti.W1p.gradient (w : RadiusTwoH1) z)
          ∂(volume : Measure R3)) := hInt
    _ = _ := congrArg (fun t : ℝ => (1/2 : ℝ)*t)
      (nativePrincipalEnergy_eq_gradient_setIntegral radiusTwoOpens (principalCoefficient g)
        (w : RadiusTwoH1) (v : RadiusTwoH1)).symm

theorem nativeDirichletForcing_radiusTwo_rescaling (f : RadiusTwoL2) (w : RadiusTwoH1Zero) :
    TauCeti.PDE.dirichletForcing f w =
      8 * TauCeti.PDE.dirichletForcing (radiusTwoNativeL2Dilation f) (radiusTwoNativeZeroDilation w) := by
  have hValue :
      (TauCeti.W1p.value (radiusTwoNativeZeroDilation w : BallH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict ballOpens]
          (fun x : R3 => TauCeti.W1p.value (w : RadiusTwoH1) ((2 : ℝ) • x)) := by
    filter_upwards [radiusTwoNativeL2Dilation_apply_ae (TauCeti.W1p.value (w : RadiusTwoH1))] with x hp
    have he := congrArg (fun q : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => (q : R3 → ℝ) x)
      (value_radiusTwoNativeZeroDilation w)
    exact he.trans hp
  have hInt := setIntegral_product_radiusTwo_transport
    (f : R3 → ℝ) (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
    (radiusTwoNativeL2Dilation f : R3 → ℝ)
    (TauCeti.W1p.value (radiusTwoNativeZeroDilation w : BallH1) : R3 → ℝ)
    (radiusTwoNativeL2Dilation_apply_ae f) hValue
  calc
    _ = ∫ z in radiusTwoOpens, f z * TauCeti.W1p.value (w : RadiusTwoH1) z
        ∂(volume : Measure R3) := TauCeti.PDE.dirichletForcing_apply_eq_setIntegral f w
    _ = 8 * (∫ x in ballOpens, radiusTwoNativeL2Dilation f x *
        TauCeti.W1p.value (radiusTwoNativeZeroDilation w : BallH1) x ∂(volume : Measure R3)) := hInt
    _ = _ := congrArg (fun t : ℝ => 8*t)
      (TauCeti.PDE.dirichletForcing_apply_eq_setIntegral
        (radiusTwoNativeL2Dilation f) (radiusTwoNativeZeroDilation w)).symm

end OAI.AnisotropicCalderon.ExteriorSource
