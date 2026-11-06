import Calderon.ActualReferencePhysicalCoefficientNativeIdentity
import Calderon.PositiveMatrixPointCalculus

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator DirichletFamily.DriftBootstrap

theorem conformalReferenceFramedNormalMetric_radius_smul
    (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (q : ℝ) (y z : R3) (r t : ℝ) :
    conformalReferenceFramedNormalMetric g L Φ (q,((y,r),t • z)) =
      conformalReferenceFramedNormalMetric g L Φ (q,((y,t),r • z)) := by
  simp only [conformalReferenceFramedNormalMetric, parameterFramedNormalizedEndpointMetric,
    framedNormalizedEndpointMetric, framedEndpointParameter, normalizedEndpointMetric,
    normalizedEndpointDerivative, scaledEndpoint, map_smul, smul_smul, mul_comm]

private theorem hasFDerivAt_zero_of_hasDerivAt_smul
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (hF : DifferentiableAt ℝ F 0)
    (hLine : ∀ v : E, HasDerivAt (fun t : ℝ => F (t • v)) 0 0) :
    HasFDerivAt (𝕜 := ℝ) F 0 0 := by
  have hZero : fderiv ℝ F (0 : E) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hCurve : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hChain := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hCurve (zero_smul ℝ v).symm
    exact hChain.unique (hLine v)
  simpa only [hZero] using hF.hasFDerivAt

theorem conformalReferenceFramedNormalMetric_zero_spatialJet
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : (y,0) ∈ B) (r : ℝ) :
    conformalReferenceFramedNormalMetric g L Φ (q,((y,r),0)) =
      ContinuousLinearMap.id ℝ R3 ∧
    HasFDerivAt (𝕜 := ℝ) (fun z : R3 =>
      conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z))) 0 0 := by
  let G : R3 → R3 →L[ℝ] R3 := fun z =>
    conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z))
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.2.2.2.2.2.2.2.1
  have hSmooth : ContDiff ℝ ∞ G :=
    (contDiff_conformalReferenceFramedNormalMetric g hg L Φ hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hValue : G 0 = ContinuousLinearMap.id ℝ R3 := by
    have hScale := conformalReferenceFramedNormalMetric_radius_smul g L Φ q y (0 : R3) r 0
    simp only [smul_zero] at hScale
    exact hScale.trans
      (conformalReferenceFramedNormalMetric_zero_radialJet g hg L y0 Φ B hData q hq y hy 0).1
  refine ⟨hValue, ?_⟩
  apply hasFDerivAt_zero_of_hasDerivAt_smul G (hSmooth.differentiable (by simp) 0)
  intro z
  have hScale : (fun t : ℝ => G (t • z)) =
      (fun t : ℝ => conformalReferenceFramedNormalMetric g L Φ (q,((y,t),r • z))) := by
    funext t
    exact conformalReferenceFramedNormalMetric_radius_smul g L Φ q y z r t
  rw [hScale]
  exact (conformalReferenceFramedNormalMetric_zero_radialJet
    g hg L y0 Φ B hData q hq y hy (r • z)).2

theorem referenceNormalMetric_spatial_zero_jet
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    H ((q,(y,r)),0) = 1 ∧
    HasFDerivAt (𝕜 := ℝ) (fun z : R3 => H ((q,(y,r)),z)) 0 0 := by
  rcases hData.1 with ⟨hNormal, hRho, hRhoEps, _, _, _, hSmoothH, _, _, _, _, hLocal, _, _, _⟩
  rcases hNormal with ⟨hEndpoint, hEps, _, _, _, _, hGeometry, _⟩
  have hyEps : ‖y-y0‖ ≤ ε := hy.trans hRhoEps
  have hBase : (y,0) ∈ B := by
    have h := (hGeometry q hq y hyEps 0 (by simpa using hEps.le) 0 (by simp)).1
    simpa only [zero_smul] using h
  have hRaw := conformalReferenceFramedNormalMetric_zero_spatialJet
    g hg L y0 Φ B hEndpoint q hq y hBase r
  have hGerm : (fun z : R3 => H ((q,(y,r)),z)) =ᶠ[𝓝 (0 : R3)]
      (fun z : R3 => operatorMatrixMap
        (conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)))) := by
    filter_upwards [Metric.ball_mem_nhds (0 : R3) (by norm_num : 0 < (2 : ℝ))] with z hz
    exact (hLocal q hq y hy r hr z (ball_subset_closedBall hz)).1
  have hSpatialSmooth : ContDiff ℝ ∞ (fun z : R3 => H ((q,(y,r)),z)) :=
    hSmoothH.comp (contDiff_const.prodMk contDiff_id)
  have hSpatialJet : HasFDerivAt (𝕜 := ℝ) (fun z : R3 => H ((q,(y,r)),z)) 0 0 := by
    apply hasFDerivAt_zero_of_hasDerivAt_smul _ (hSpatialSmooth.differentiable (by simp) 0)
    intro v
    have hCurve : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hLine := hRaw.2.comp_hasDerivAt_of_eq 0 hCurve (zero_smul ℝ v).symm
    simp only [ContinuousLinearMap.zero_apply, Function.comp_def] at hLine
    have hMatrixLine := operatorMatrixMap.hasFDerivAt.comp_hasDerivAt 0 hLine
    simp only [map_zero, Function.comp_def] at hMatrixLine
    have hT : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 (0 : R3)) := by
      simpa using hCurve.continuousAt.tendsto
    exact hMatrixLine.congr_of_eventuallyEq (hGerm.comp_tendsto hT)
  refine ⟨?_, hSpatialJet⟩
  rw [(hLocal q hq y hy r hr 0 (by simp)).1]
  change operatorMatrixMap (conformalReferenceFramedNormalMetric g L Φ (q,((y,r),0))) = 1
  rw [hRaw.1, operatorMatrixMap_id]

theorem referenceNormalPrincipalCoefficient_spatial_zero_jet
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    matrixPrincipalCoefficient H ((q,(y,r)),0) = 1 ∧
    HasFDerivAt (𝕜 := ℝ) (fun z : R3 => matrixPrincipalCoefficient H ((q,(y,r)),z)) 0 0 := by
  have hMetric := referenceNormalMetric_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  have hPos : (H ((q,(y,r)),0)).PosDef := hData.1.2.2.2.2.2.2.2.1 _
  refine ⟨?_, ?_⟩
  · simp only [matrixPrincipalCoefficient, matrixVolumeDensity, hMetric.1,
      Matrix.det_one, Real.sqrt_one, inv_one, one_smul]
  · have hSmoothH : ContDiff ℝ ∞ H := hData.1.2.2.2.2.2.2.1
    have hAllPos : ∀ p, (H p).PosDef := hData.1.2.2.2.2.2.2.2.1
    have hSmooth : ContDiff ℝ ∞ (fun z : R3 => matrixPrincipalCoefficient H ((q,(y,r)),z)) :=
      (contDiff_matrixPrincipalCoefficient H hSmoothH hAllPos).comp
        (contDiff_const.prodMk contDiff_id)
    apply hasFDerivAt_zero_of_hasDerivAt_smul _ (hSmooth.differentiable (by simp) 0)
    intro v
    have hCurve : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hLine := hMetric.2.comp_hasDerivAt_of_eq 0 hCurve (zero_smul ℝ v).symm
    simp only [ContinuousLinearMap.zero_apply, Function.comp_def] at hLine
    have h := hasDerivAt_matrixPrincipalCoefficient_zero
      (fun t : ℝ => H ((q,(y,r)),t • v)) 0 hLine (hAllPos _)
    exact h

theorem referenceNativePrincipalCoefficient_spatial_zero_jet
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    a ((q,(y,r)),0) = 1 ∧
    HasFDerivAt (𝕜 := ℝ) (fun z : R3 => a ((q,(y,r)),z)) 0 0 := by
  have hPrincipal := referenceNormalPrincipalCoefficient_spatial_zero_jet
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr
  have hGerm : (fun z : R3 => a ((q,(y,r)),z)) =ᶠ[𝓝 (0 : R3)]
      (fun z : R3 => matrixPrincipalCoefficient H ((q,(y,r)),z)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : R3) (by norm_num : 0 < (2 : ℝ))] with z hz
    exact nativePrincipal_eq_matrixPrincipal_on_doubleBall
      g L y0 Φ B ε C ρ H a w hData q hq y hy r hr z (ball_subset_closedBall hz)
  refine ⟨?_, hPrincipal.2.congr_of_eventuallyEq hGerm⟩
  rw [nativePrincipal_eq_matrixPrincipal_on_doubleBall
    g L y0 Φ B ε C ρ H a w hData q hq y hy r hr 0 (by simp)]
  exact hPrincipal.1

theorem referenceNormalPrincipalCoefficients_spatial_fderiv_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) :
    fderiv ℝ (fun z : R3 => matrixPrincipalCoefficient H ((q,(y,r)),z)) 0 = 0 ∧
    fderiv ℝ (fun z : R3 => a ((q,(y,r)),z)) 0 = 0 := by
  exact ⟨(referenceNormalPrincipalCoefficient_spatial_zero_jet
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr).2.fderiv,
    (referenceNativePrincipalCoefficient_spatial_zero_jet
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr).2.fderiv⟩

end OAI.AnisotropicCalderon.ConnectionError
