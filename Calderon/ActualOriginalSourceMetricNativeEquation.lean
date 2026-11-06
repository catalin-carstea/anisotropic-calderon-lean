import Calderon.ActualOriginalSourceMetricGeometry
import Calderon.ActualFiberRawFluxGauge

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ConnectionError MetricVolume MetricOperator DirichletFamily.DriftBootstrap

theorem principalCoefficient_originalSourcePacketMetricModel
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : 0 < lam) (y : R3) (r : ℝ) (hr : 0 < r) (z : R3) :
    principalCoefficient (originalSourcePacketMetricModel S L P lam y r) z =
      (lam*r) • referencePhysicalNormalizedPrincipalCoefficient S.g1 L P.Phi P.H (lam,(y,r)) z := by
  rcases P.native_data.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
  rw [originalSourcePacketMetricModel,principalCoefficient_conformalMatrix _ _
    (fun x => hPos ((lam,(y,r)),x)) z]
  rw [Real.exp_add,Real.exp_log (mul_pos hlam hr),mul_smul]
  rfl

theorem originalSourcePacketMetricModel_harmonic_of_native_normalized
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : 0 < lam) (y : R3) (r : ℝ) (hr : 0 < r)
    (v : SmoothData)
    (hNative : ∀ z ∈ ball (0 : R3) 1, coordinateFluxDivergence (fun x => matrixOperatorMap
      (referencePhysicalNormalizedPrincipalCoefficient S.g1 L P.Phi P.H (lam,(y,r)) x)
      (gradient v.1 x : R3)) z = 0) :
    ∀ z ∈ ball (0 : R3) 1, coordinateFluxDivergence
      (metricDivergenceFlux (originalSourcePacketMetricModel S L P lam y r) v.1) z = 0 := by
  let g := originalSourcePacketMetricModel S L P lam y r
  let c := lam*r
  let Z : R3 → R3 := fun x => matrixOperatorMap
    (referencePhysicalNormalizedPrincipalCoefficient S.g1 L P.Phi P.H (lam,(y,r)) x)
    (gradient v.1 x : R3)
  have hc : 0 < c := mul_pos hlam hr
  have hFlux : metricDivergenceFlux g v.1 = fun x => c • Z x := by
    funext x
    unfold metricDivergenceFlux
    rw [principalCoefficient_originalSourcePacketMetricModel S L P lam hlam y r hr x,map_smul,
      ContinuousLinearMap.smul_apply]
  have hMetric := originalSourcePacketMetricModel_smooth_positive S L P lam y r
  have hQ : ContDiff ℝ ∞ (metricDivergenceFlux g v.1) :=
    contDiff_metricDivergenceFlux g hMetric.1 hMetric.2 v.1 v.2
  have hZeq : Z = fun x => c⁻¹ • metricDivergenceFlux g v.1 x := by
    funext x
    rw [hFlux]
    simp only [smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
  have hZ : ContDiff ℝ ∞ Z := by
    rw [hZeq]
    exact ContDiff.const_smul c⁻¹ hQ
  intro z hz
  have hScale := coordinateFluxDivergence_exp_depth (fun _ : R3 => Real.log c)
    Z (-1) z (differentiableAt_const _) (hZ.differentiable (by simp) z)
  have hDiv : coordinateFluxDivergence (fun x => c • Z x) z = c * coordinateFluxDivergence Z z := by
    simpa only [neg_neg,one_mul,Real.exp_log hc,fderiv_const_apply,zero_apply,mul_zero,sub_zero] using hScale
  rw [hFlux,hDiv,hNative z hz,mul_zero]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
