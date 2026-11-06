import Calderon.ActualReferencePhysicalOrientation
import Calderon.ActualReferenceGaugePrincipalFamily
import Calderon.ActualMetricWronskianDivergence
import Calderon.ActualPhysicalBoundaryChainRule
import Calderon.NativeCoefficientFluxTrace

/-! No harmonicity or inverse premise is used. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic MetricVolume MetricOperator

def smoothCoefficientConormalSphere (F : SmoothCoefficientMatrix 2) (f : SmoothData) :
    C(UnitSphere, ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3, sphereCoordinate i *
    (smoothSphereValue (coefficientSmoothData (F i j)) *
      smoothSphereValue (smoothCoordinateDerivative f j))

lemma ordinaryConormalTraceL_smoothBallSobolev
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (f : SmoothData) :
    ordinaryConormalTraceL hcalc τ0 F (smoothBallSobolev 2 f) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothCoefficientConormalSphere F f) := by
  rw [ordinaryConormalTraceL_eq_sphere_coefficient_trace]
  simp only [smoothCoefficientConormalSphere,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [strongCoordinateTraceL_smooth hcalc τ0 j f,
    sphereContinuousScalarMulL_toLp,sphereCoordinateMulL_toLp]

lemma smoothCoefficientConormalSphere_apply
    (F : SmoothCoefficientMatrix 2) (f : SmoothData) (theta : UnitSphere) :
    smoothCoefficientConormalSphere F f theta =
      inner ℝ theta.val (matrixOperatorMap (coefficientMatrixField 2 F theta.val)
        (gradient f.1 theta.val)) := by
  simp only [smoothCoefficientConormalSphere,ContinuousMap.sum_apply,
    ContinuousMap.mul_apply,sphereCoordinate,smoothSphereValue,coefficientSmoothData,
    smoothCoordinateDerivative]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,star_trivial,matrixOperator_coordinate,gradient_coordinate,
    coefficientMatrixField]
  simp only [Finset.sum_mul,ContinuousMap.coe_mk]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change theta.val i * (coefficientValue 2 (F i j) theta.val *
    fderiv ℝ f.1 theta.val (coordinateVector j)) =
      coefficientValue 2 (F i j) theta.val *
        fderiv ℝ f.1 theta.val (coordinateVector j) * theta.val i
  ring

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap
  SphereHarmonic NativePolynomialBulkMoments

lemma signedPiolaFlux_metricWronskianFlux_of_det_pos
    (g : MatrixField) (X : R3 → R3) (u v : R3 → ℝ)
    (hX : ContDiff ℝ ∞ X) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (x : R3) (hdet : 0 < (coordinateJacobianMatrix X x).det) :
    signedPiolaFlux X (metricWronskianFlux g u v) x =
      metricWronskianFlux (pullbackMetric g X) (u ∘ X) (v ∘ X) x := by
  rw [metricWronskianFlux,
    metricDivergenceFlux_pullbackMetric_eq_signedPiolaFlux_of_det_pos g X u hX hu x hdet,
    metricDivergenceFlux_pullbackMetric_eq_signedPiolaFlux_of_det_pos g X v hX hv x hdet]
  simp only [signedPiolaFlux,metricWronskianFlux,map_sub,map_smul,Function.comp_apply]

lemma integral_smoothCoefficientWronskian_surface_eq_trace_pairing
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 2) (u v : SmoothData) :
    (∫ theta : UnitSphere,
      v.1 theta.val * smoothCoefficientConormalSphere F u theta -
        u.1 theta.val * smoothCoefficientConormalSphere F v theta ∂surfaceMeasure) =
      sphereSurfaceMass *
        (inner ℝ (τ0.valueTraceL (smoothSobolev v))
          (ordinaryConormalTraceL hcalc τ0 F (smoothBallSobolev 2 u)) -
        inner ℝ (ordinaryConormalTraceL hcalc τ0 F (smoothBallSobolev 2 v))
          (τ0.valueTraceL (smoothSobolev u))) := by
  have hIu : Integrable (fun theta : UnitSphere =>
      v.1 theta.val * smoothCoefficientConormalSphere F u theta) sphereProbability :=
    ((smoothSphereValue v).continuous.mul (smoothCoefficientConormalSphere F u).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIv : Integrable (fun theta : UnitSphere =>
      u.1 theta.val * smoothCoefficientConormalSphere F v theta) sphereProbability :=
    ((smoothSphereValue u).continuous.mul (smoothCoefficientConormalSphere F v).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_surface_eq_mass_probability,integral_sub hIu hIv,
    ordinaryConormalTraceL_smoothBallSobolev,ordinaryConormalTraceL_smoothBallSobolev,
    τ0.valueTrace_smooth v,τ0.valueTrace_smooth u,
    ContinuousMap.inner_toLp sphereProbability (smoothSphereValue v) (smoothCoefficientConormalSphere F u),
    ContinuousMap.inner_toLp sphereProbability (smoothCoefficientConormalSphere F v) (smoothSphereValue u)]
  congr 1
  congr 1
  · apply integral_congr_ae
    exact ae_of_all sphereProbability (fun theta => by
      simp only [starRingEnd_apply,star_trivial]
      change v.1 theta.val * smoothCoefficientConormalSphere F u theta =
        smoothCoefficientConormalSphere F u theta * v.1 theta.val
      ring)

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData in
lemma principalCoefficient_referencePhysicalPullback_eq_radius_nativeGauge
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hrpos : 0 < r)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    principalCoefficient (pullbackMetric (fun x => g (q • x))
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))) z =
      r • coefficientMatrixField 2
        (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))) z := by
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets]
  dsimp only
  rw [referencePhysicalGaugeCompactPrincipalCoefficient_eq_weighted_native
    g L y0 Φ B ε C ρ H a w hData]
  exact principalCoefficient_referencePhysicalPullback_eq_pos_radius_smul_native
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hrpos z hz

include hg hData in
lemma signedPiolaFlux_reference_metricWronskianFlux_on_sphere
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hrpos : 0 < r) (u v : SmoothData)
    (theta : UnitSphere) :
    let U := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u
    let V := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v
    let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))
    inner ℝ theta.val (signedPiolaFlux
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))
      (metricWronskianFlux (fun x => g (q • x)) u.1 v.1) theta.val) =
      r * (V.1 theta.val * smoothCoefficientConormalSphere F U theta -
        U.1 theta.val * smoothCoefficientConormalSphere F V theta) := by
  dsimp only
  let X : R3 → R3 := fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x))
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk ((contDiff_const.prodMk contDiff_const).prodMk contDiff_id))
  have hz : theta.val ∈ closedBall (0 : R3) 2 := by
    have hn : ‖theta.val‖ = 1 := by
      simpa only [mem_sphere,dist_zero_right] using theta.property
    simp only [mem_closedBall,dist_zero_right,hn]
    norm_num
  have hd := coordinateJacobianMatrix_referencePhysicalEndpoint_det_pos
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hrpos theta.val hz
  rw [signedPiolaFlux_metricWronskianFlux_of_det_pos (fun x => g (q • x)) X u.1 v.1
    hX u.2 v.2 theta.val hd]
  simp only [metricWronskianFlux,inner_sub_right,inner_smul_right]
  rw [smoothCoefficientConormalSphere_apply,smoothCoefficientConormalSphere_apply]
  have hA := principalCoefficient_referencePhysicalPullback_eq_radius_nativeGauge
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hrpos theta.val hz
  change principalCoefficient (pullbackMetric (fun x => g (q • x)) X) theta.val = _ at hA
  simp only [metricDivergenceFlux]
  rw [hA]
  simp only [map_smul,smul_apply,inner_smul_right]
  change v.1 (X theta.val) * (r * inner ℝ theta.val
      (matrixOperatorMap _ (gradient (u.1 ∘ X) theta.val))) -
    u.1 (X theta.val) * (r * inner ℝ theta.val
      (matrixOperatorMap _ (gradient (v.1 ∘ X) theta.val))) =
    r * (v.1 (X theta.val) * inner ℝ theta.val
      (matrixOperatorMap _ (gradient (u.1 ∘ X) theta.val)) -
    u.1 (X theta.val) * inner ℝ theta.val
      (matrixOperatorMap _ (gradient (v.1 ∘ X) theta.val)))
  ring

include hg hData in
/-- Exact nonharmonic physical signed-Piola Wronskian/native conormal pairing.
The sphere integral retains the physical surface measure and its full mass. -/
theorem integral_signedPiolaFlux_reference_metricWronskianFlux_eq_native_pairing
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hrpos : 0 < r) (u v : SmoothData) :
    let U := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u
    let V := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v
    let F := referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r))
    (∫ theta : UnitSphere, inner ℝ theta.val (signedPiolaFlux
      (fun x => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),x)))
      (metricWronskianFlux (fun x => g (q • x)) u.1 v.1) theta.val) ∂surfaceMeasure) =
      r * sphereSurfaceMass *
        (inner ℝ (τ0.valueTraceL (smoothSobolev V))
          (ordinaryConormalTraceL hcalc τ0 F (smoothBallSobolev 2 U)) -
        inner ℝ (ordinaryConormalTraceL hcalc τ0 F (smoothBallSobolev 2 V))
          (τ0.valueTraceL (smoothSobolev U))) := by
  dsimp only
  calc
    _ = ∫ theta : UnitSphere, r *
        ((referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v).1 theta.val *
          smoothCoefficientConormalSphere
            (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)))
            (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u) theta -
        (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u).1 theta.val *
          smoothCoefficientConormalSphere
            (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData 2 (q,(y,r)))
            (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v) theta) ∂surfaceMeasure := by
      apply integral_congr_ae
      exact ae_of_all surfaceMeasure (fun theta =>
        signedPiolaFlux_reference_metricWronskianFlux_on_sphere
          g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hrpos u v theta)
    _ = _ := by
      rw [integral_const_mul,integral_smoothCoefficientWronskian_surface_eq_trace_pairing hcalc τ0]
      ring

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.integral_signedPiolaFlux_reference_metricWronskianFlux_eq_native_pairing
