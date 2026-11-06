import Calderon.ActualReferenceSpatialNormalJets
import Calderon.ActualReferenceHalfGaugeCalculus
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


theorem referenceRescaledDepth_radius_zero_const
    (q : ℝ) (y z : R3) :
    referenceRescaledDepth g L Φ (q,(y,0)) z = referenceRescaledDepth g L Φ (q,(y,0)) 0 := by
  simp only [referenceRescaledDepth, parameterFramedScaledEndpoint, framedScaledEndpoint,
    scaledEndpoint, framedEndpointParameter, zero_smul]


theorem referencePhysicalHalfGauge_radius_zero_const
    (q : ℝ) (y z : R3) :
    referencePhysicalHalfGauge g L Φ ((q,(y,0)),z) = referencePhysicalHalfGauge g L Φ ((q,(y,0)),0) := by
  unfold referencePhysicalHalfGauge
  rw [referenceRescaledDepth_radius_zero_const g L Φ q y z]


include hg hData in
theorem referenceNormalMetric_radius_zero_on_doubleBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    H ((q,(y,0)),z) = 1 := by
  rcases hData.1 with ⟨hNormal, hRho, hRhoEps, _, _, _, _, _, _, _, _, hLocal, _, _, _⟩
  rcases hNormal with ⟨hEndpoint, hEps, _, _, _, _, hGeometry, _⟩
  have hr0 : |(0 : ℝ)| ≤ 4*ρ := by
    simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hRho.le
  have hyEps : ‖y-y0‖ ≤ ε := hy.trans hRhoEps
  have hBase : (y,0) ∈ B := by
    have h := (hGeometry q hq y hyEps 0 (by simpa using hEps.le) 0 (by simp)).1
    simpa only [zero_smul] using h
  have hRaw := (conformalReferenceFramedNormalMetric_zero_radialJet
    g hg L y0 Φ B hEndpoint q hq y hBase z).1
  rw [(hLocal q hq y hy 0 hr0 z hz).1]
  change operatorMatrixMap (conformalReferenceFramedNormalMetric g L Φ (q,((y,0),z))) = 1
  rw [hRaw,operatorMatrixMap_id]


include hg hData in
theorem referenceNativePrincipalCoefficient_radius_zero_on_unitBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 1) :
    a ((q,(y,0)),z) = 1 := by
  have hRho : 0 < ρ := hData.1.2.1
  have hr0 : |(0 : ℝ)| ≤ 4*ρ := by
    simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hRho.le
  have hz2 : z ∈ closedBall (0 : R3) 2 := closedBall_subset_closedBall (by norm_num) hz
  rw [nativePrincipal_eq_matrixPrincipal_on_doubleBall
    g L y0 Φ B ε C ρ H a w hData q hq y hy 0 hr0 z hz2]
  simp only [matrixPrincipalCoefficient, matrixVolumeDensity,
    referenceNormalMetric_radius_zero_on_doubleBall g hg L y0 Φ B ε C ρ H a w hData q hq y hy z hz2,
    Matrix.det_one, Real.sqrt_one, inv_one, one_smul]


include hg hData in
theorem referencePhysicalGaugeCompactPrincipalCoefficient_radius_zero_on_unitBall
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 1) :
    referencePhysicalGaugeCompactPrincipalCoefficient g L Φ H ((q,(y,0)),z) =
      (referencePhysicalHalfGauge g L Φ ((q,(y,0)),0))^2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [← referencePhysicalHalfGauge_sq_smul_native g L y0 Φ B ε C ρ H a w hData ((q,(y,0)),z),
    referencePhysicalHalfGauge_radius_zero_const g L Φ q y z,
    referenceNativePrincipalCoefficient_radius_zero_on_unitBall g hg L y0 Φ B ε C ρ H a w hData q hq y hy z hz]


include hg hData in
theorem coefficientMatrixField_referencePhysicalGaugeCoefficientJets_radius_zero_on_unitBall
    (k : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 1) :
    coefficientMatrixField k (referencePhysicalGaugeCoefficientJets g hg L y0 Φ B ε C ρ H a w hData k (q,(y,0))) z =
      (referencePhysicalHalfGauge g L Φ ((q,(y,0)),0))^2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [coefficientMatrixField_referencePhysicalGaugeCoefficientJets]
  exact referencePhysicalGaugeCompactPrincipalCoefficient_radius_zero_on_unitBall
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy z hz

end OAI.AnisotropicCalderon.ConnectionError
