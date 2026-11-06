import Calderon.ActualSourceFrontierCovectorGram
import Calderon.ActualSourceChartNativeFirstDerivative
import Calderon.NativeSourceChartInverseConditioning

/-! Two charts of the same source remain distinct. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Distributions Matrix BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ConnectionError MetricOperator MetricVolume FixedSourceJetFrame

lemma coordinateJacobianMatrix_radiusTwoSourceEuclideanCoordinates
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ)) (p : R3)
    (hp : p ∈ (radiusTwoOpens : Set R3)) :
    coordinateJacobianMatrix
      (radiusTwoSourceEuclideanCoordinates fixedDirichletRegularity fixedSobolevCalculus g hg f) p =
      Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
        fixedDirichletRegularity fixedSobolevCalculus g hg (f i)) p j) := by
  unfold coordinateJacobianMatrix
  rw [(hasFDerivAt_radiusTwoSourceEuclideanCoordinates_sum_smulRight g hg f p hp).fderiv]
  ext i j
  change ((∑ k : Fin 3, (fderiv ℝ (radiusTwoSmoothSourceResponse
    fixedDirichletRegularity fixedSobolevCalculus g hg (f k)) p).smulRight
      (coordinateVector k)) (coordinateVector j)) i = _
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  fin_cases i <;> simp [Fin.sum_univ_three, coordinateVector, PiLp.single_apply, d]

/-- At a known-phase limit, each metric is pulled through its OWN SAME-source chart.
The second chart derivative is only assumed differentiable, never equal to Id. -/
theorem pullbackMetric_same_source_charts_eq_of_limit_match
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (f : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (Phi : R3 → R3) (W : Set R3) (hW : IsOpen W) (x q : R3)
    (hx : x ∈ (radiusTwoOpens : Set R3)) (hq : q ∈ (radiusTwoOpens : Set R3))
    (hClosure : x ∈ closure W) (hLimit : Tendsto Phi (𝓝[W] x) (𝓝 q))
    (hMaps : ∀ y ∈ W, Phi y ∈ (radiusTwoOpens : Set R3))
    (hDiff : ∀ y ∈ W, DifferentiableAt ℝ Phi y)
    (hMatch : ∀ y ∈ W, ∀ source : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 source y =
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 source (Phi y))
    (hMetric : ∀ y ∈ W, g2 y = (D Phi y)ᵀ * g1 (Phi y) * D Phi y)
    (e1 e2 : OpenPartialHomeomorph R3 R3)
    (he1 : (e1 : R3 → R3) = radiusTwoSourceEuclideanCoordinates
      fixedDirichletRegularity fixedSobolevCalculus g1 hg1 f)
    (he2 : (e2 : R3 → R3) = radiusTwoSourceEuclideanCoordinates
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 f)
    (hqSource : q ∈ e1.source) (hxSource : x ∈ e2.source)
    (hDe1 : DifferentiableAt ℝ (e1 : R3 → R3) q)
    (hDe2 : DifferentiableAt ℝ (e2 : R3 → R3) x)
    (hInv1 : DifferentiableAt ℝ (e1.symm : R3 → R3) (e1 q))
    (hInv2 : DifferentiableAt ℝ (e2.symm : R3 → R3) (e2 x)) :
    pullbackMetric g2 (e2.symm : R3 → R3) (e1 q) =
      pullbackMetric g1 (e1.symm : R3 → R3) (e1 q) := by
  letI : NeBot (𝓝[W] x) := mem_closure_iff_nhdsWithin_neBot.mp hClosure
  have hPoint (y : R3) (hy : y ∈ W) : e2 y = e1 (Phi y) := by
    rw [he1, he2]
    have hValues : radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus g2 hg2 f y =
        radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus g1 hg1 f (Phi y) := by
      funext i
      exact hMatch y hy (f i)
    exact congrArg (fun v : Fin 3 → ℝ => (EuclideanSpace.equiv (Fin 3) ℝ).symm v) hValues
  have hSame : e2 x = e1 q := by
    have hLeft : Tendsto (e2 : R3 → R3) (𝓝[W] x) (𝓝 (e2 x)) :=
      hDe2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hRight := hDe1.continuousAt.tendsto.comp hLimit
    have hEqual : (e2 : R3 → R3) =ᶠ[𝓝[W] x] (fun y => e1 (Phi y)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hPoint y hy
    exact tendsto_nhds_unique_of_eventuallyEq hLeft hRight hEqual
  let z : R3 := e1 q
  have hb1 : e1.symm z = q := e1.left_inv hqSource
  have hb2 : e2.symm z = x := by
    change e2.symm (e1 q) = x
    rw [← hSame]
    exact e2.left_inv hxSource
  let K1 := operatorMatrixMap (fderiv ℝ (e1 : R3 → R3) q)
  let K2 := operatorMatrixMap (fderiv ℝ (e2 : R3 → R3) x)
  let L1 := operatorMatrixMap (fderiv ℝ (e1.symm : R3 → R3) z)
  let L2 := operatorMatrixMap (fderiv ℝ (e2.symm : R3 → R3) z)
  have hK1 : K1 = Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g1 hg1 (f i)) q j) := by
    dsimp only [K1]
    rw [← coordinateJacobianMatrix_eq_operatorMatrixMap, he1]
    exact coordinateJacobianMatrix_radiusTwoSourceEuclideanCoordinates g1 hg1 f q hq
  have hK2 : K2 = Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 (f i)) x j) := by
    dsimp only [K2]
    rw [← coordinateJacobianMatrix_eq_operatorMatrixMap, he2]
    exact coordinateJacobianMatrix_radiusTwoSourceEuclideanCoordinates g2 hg2 f x hx
  have hGram := radiusTwoSourceCovectorGram_eq_of_limit_match
    fixedDirichletRegularity fixedSobolevCalculus g1 hg1 g2 hg2 f Phi W hW x q hx hq
      hClosure hLimit hMaps hDiff hMatch hMetric
  change Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 (f i)) x j) *
      (g2 x)⁻¹ * (Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
        fixedDirichletRegularity fixedSobolevCalculus g2 hg2 (f i)) x j))ᵀ =
    Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
      fixedDirichletRegularity fixedSobolevCalculus g1 hg1 (f i)) q j) *
      (g1 q)⁻¹ * (Matrix.of (fun i j => d (radiusTwoSmoothSourceResponse
        fixedDirichletRegularity fixedSobolevCalculus g1 hg1 (f i)) q j))ᵀ at hGram
  rw [← hK1, ← hK2] at hGram
  have hId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) := matrixOperatorAlgEquiv.symm.map_one
  have hKL1 : K1 * L1 = 1 := by
    have hDf : DifferentiableAt ℝ (e1 : R3 → R3) (e1.symm z) := by
      simpa only [hb1] using hDe1
    have hComp := NativeSourceChartCalculus.comp_eq_id_of_same_chart_hasFDerivAt
      (e1 : R3 → R3) e1 z (e1.map_source hqSource) rfl _ _
      hDf.hasFDerivAt hInv1.hasFDerivAt
    have hM := congrArg operatorMatrixMap hComp
    simpa only [hb1, operatorMatrixMap_comp, hId] using hM
  have hKL2 : K2 * L2 = 1 := by
    have hz2 : z ∈ e2.target := by
      change e1 q ∈ e2.target
      rw [← hSame]
      exact e2.map_source hxSource
    have hDf : DifferentiableAt ℝ (e2 : R3 → R3) (e2.symm z) := by
      simpa only [hb2] using hDe2
    have hInv2z : DifferentiableAt ℝ (e2.symm : R3 → R3) z := by
      simpa only [hSame] using hInv2
    have hComp := NativeSourceChartCalculus.comp_eq_id_of_same_chart_hasFDerivAt
      (e2 : R3 → R3) e2 z hz2 rfl _ _ hDf.hasFDerivAt hInv2z.hasFDerivAt
    have hM := congrArg operatorMatrixMap hComp
    simpa only [hb2, operatorMatrixMap_comp, hId] using hM
  have hL1 : K1⁻¹ = L1 := Matrix.inv_eq_right_inv hKL1
  have hL2 : K2⁻¹ = L2 := Matrix.inv_eq_right_inv hKL2
  have hG1 : ((g1 q)⁻¹)⁻¹ = g1 q := by
    letI := Matrix.invertibleOfIsUnitDet (g1 q)
      (isUnit_iff_ne_zero.mpr (hg1.posDef q).det_pos.ne')
    exact Matrix.inv_inv_of_invertible _
  have hG2 : ((g2 x)⁻¹)⁻¹ = g2 x := by
    letI := Matrix.invertibleOfIsUnitDet (g2 x)
      (isUnit_iff_ne_zero.mpr (hg2.posDef x).det_pos.ne')
    exact Matrix.inv_inv_of_invertible _
  have hInverse := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M⁻¹) hGram
  have hFinal : L2ᵀ * g2 x * L2 = L1ᵀ * g1 q * L1 := by
    simpa only [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      hG1, hG2, hL1, hL2, Matrix.mul_assoc] using hInverse
  change pullbackMetric g2 (e2.symm : R3 → R3) z =
    pullbackMetric g1 (e1.symm : R3 → R3) z
  simp only [pullbackMetric, operatorMatrixMap_comp, operatorMatrixMap_adjoint,
    operatorMatrixMap_metricOperatorField]
  change L2ᵀ * (g2 (e2.symm z) * L2) = L1ᵀ * (g1 (e1.symm z) * L1)
  rw [hb2, hb1]
  simpa only [Matrix.mul_assoc] using hFinal

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.coordinateJacobianMatrix_radiusTwoSourceEuclideanCoordinates
#print axioms OAI.AnisotropicCalderon.ExteriorSource.pullbackMetric_same_source_charts_eq_of_limit_match
