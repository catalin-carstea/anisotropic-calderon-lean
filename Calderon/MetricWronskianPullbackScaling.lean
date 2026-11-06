import Calderon.ActualMetricWronskianDivergence
import Calderon.ActualReferencePhysicalCoefficientNativeIdentity

set_option autoImplicit false
noncomputable section
open Filter Function
open scoped Topology Gradient ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator

theorem metricWronskianFlux_congr_right_of_eventuallyEq
    (g : MatrixField) (u f h : R3 → ℝ) (x : R3) (hNear : f =ᶠ[𝓝 x] h) :
    metricWronskianFlux g u f x = metricWronskianFlux g u h x := by
  simp only [metricWronskianFlux,metricDivergenceFlux,hNear.eq_of_nhds,hNear.gradient_eq]

theorem metricWronskianFlux_scaled_coefficient_reciprocal_kernel
    (g h : MatrixField) (c : ℝ) (hc : c ≠ 0) (u f : R3 → ℝ) (x : R3)
    (hf : DifferentiableAt ℝ f x)
    (hCoeff : principalCoefficient g x = c • principalCoefficient h x) :
    metricWronskianFlux g u (fun z => c⁻¹*f z) x = metricWronskianFlux h u f x := by
  have hGrad : (gradient (fun z => c⁻¹*f z) x : R3) = c⁻¹ • (gradient f x : R3) := by
    ext i
    rw [gradient_coordinate,PiLp.smul_apply,gradient_coordinate]
    rw [(hf.hasFDerivAt.const_mul c⁻¹).fderiv]
    rfl
  simp only [metricWronskianFlux,metricDivergenceFlux,hCoeff,map_smul,
    ContinuousLinearMap.smul_apply,hGrad,smul_smul]
  ext i
  simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp [hc] <;> ring

theorem metricWronskianFlux_pullbackMetric_eq_signedPiolaFlux
    (g : MatrixField) (X : R3 → R3) (u v : R3 → ℝ)
    (hX : ContDiff ℝ ∞ X) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (x : R3) (hdet : 0 < (coordinateJacobianMatrix X x).det) :
    metricWronskianFlux (pullbackMetric g X) (u ∘ X) (v ∘ X) x =
      signedPiolaFlux X (metricWronskianFlux g u v) x := by
  simp only [metricWronskianFlux,
    metricDivergenceFlux_pullbackMetric_eq_signedPiolaFlux_of_det_pos g X u hX hu x hdet,
    metricDivergenceFlux_pullbackMetric_eq_signedPiolaFlux_of_det_pos g X v hX hv x hdet,
    Function.comp_apply,signedPiolaFlux,map_sub,map_smul]

end OAI.AnisotropicCalderon.ConnectionError
