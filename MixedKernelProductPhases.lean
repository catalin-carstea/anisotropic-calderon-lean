import MixedKernelUnitStrictSource
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open MetricOperator MetricVolume ConnectionError
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Operator

/-- The exact native joint hypersurface test from the selected source criterion. -/
def ProductHessianStrictAt (g1 g2 : MatrixField) (x0 y0 : R3) (rho : R3 × R3 → ℝ) : Prop :=
  let ell : R3 × R3 →L[ℝ] ℝ := fderiv ℝ rho (x0,y0)
  let ell1 : R3 →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inl ℝ R3 R3)
  let ell2 : R3 →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inr ℝ R3 R3)
  let M1 : R3 →L[ℝ] R3 := MetricOperator.metricOperatorField g1 x0
  let M2 : R3 →L[ℝ] R3 := MetricOperator.metricOperatorField g2 y0
  let Gamma1 : R3 →L[ℝ] R3 →L[ℝ] R3 := ConnectionError.coordinateConnectionField
    (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g1))
    (MetricOperator.metricOperatorField g1) x0
  let Gamma2 : R3 →L[ℝ] R3 →L[ℝ] R3 := ConnectionError.coordinateConnectionField
    (ConnectionError.inverseMetricField (MetricOperator.metricOperatorField g2))
    (MetricOperator.metricOperatorField g2) y0
  let b1 : R3 := MetricOperator.matrixOperatorMap ((g1 x0)⁻¹)
    (WithLp.toLp 2 (fun i : Fin 3 => ell1 (coordinateVector i)))
  let b2 : R3 := MetricOperator.matrixOperatorMap ((g2 y0)⁻¹)
    (WithLp.toLp 2 (fun i : Fin 3 => ell2 (coordinateVector i)))
  let a1 : R3 := (⟪M1 b1,b1⟫_ℝ)⁻¹ • b1
  let a2 : R3 := (⟪M2 b2,b2⟫_ℝ)⁻¹ • b2
  let H : (R3 × R3) → (R3 × R3) → ℝ := fun X Y =>
    fderiv ℝ (fderiv ℝ rho) (x0,y0) X Y -
      ell (Gamma1 X.1 Y.1,Gamma2 X.2 Y.2)
  ell1 ≠ 0 ∧ ell2 ≠ 0 ∧
  (∀ v1 v2 : R3,
    ⟪M1 v1,a1⟫_ℝ = 0 → ⟪M1 v1,v1⟫_ℝ = ⟪M1 a1,a1⟫_ℝ →
    ⟪M2 v2,a2⟫_ℝ = 0 → ⟪M2 v2,v2⟫_ℝ = ⟪M2 a2,a2⟫_ℝ →
    0 < H (a1,-a2) (a1,-a2) + H (v1,v2) (v1,v2))

/-- The actual joint Hessian test produces the SAME two strict phases and quadratic gap
needed by the native room interpolation and current-side cross placement. -/
theorem exists_native_product_strict_phases
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (x0 y0 : R3) (U : Set (R3 × R3)) (hU : IsOpen U) (hpU : (x0,y0) ∈ U)
    (rho : R3 × R3 → ℝ) (hrho : ContDiffOn ℝ ∞ rho U) (hrho0 : rho (x0,y0) = 0)
    (hTest : ProductHessianStrictAt g1 g2 x0 y0 rho) :
    ∃ (θ1 θ2 : R3 → ℝ) (c r K : ℝ),
      ContDiff ℝ ∞ θ1 ∧ ContDiff ℝ ∞ θ2 ∧ θ1 x0 = 0 ∧ θ2 y0 = 0 ∧
      fderiv ℝ θ1 x0 = (fderiv ℝ rho (x0,y0)).comp (ContinuousLinearMap.inl ℝ R3 R3) ∧
      fderiv ℝ θ2 y0 = (fderiv ℝ rho (x0,y0)).comp (ContinuousLinearMap.inr ℝ R3 R3) ∧
      (fun k => pd k θ1 x0) ≠ 0 ∧ (fun k => pd k θ2 y0) ≠ 0 ∧
      SrcStrict g1 θ1 x0 ∧ SrcStrict g2 θ2 y0 ∧
      0 < c ∧ 0 < r ∧ 0 < K ∧ Metric.closedBall (x0,y0) r ⊆ U ∧
      (∀ z ∈ Metric.closedBall (x0,y0) r,
        θ1 z.1 + θ2 z.2 ≤ rho z + K * rho z ^ 2 / 2 -
          c * (‖z.1-x0‖ ^ 2 + ‖z.2-y0‖ ^ 2)) ∧
      (∀ z ∈ Metric.closedBall (x0,y0) r,
        (0 < rho z + K * rho z ^ 2 / 2 ↔ 0 < rho z)) := by
  have hdiff1 : ∀ i j, DifferentiableAt ℝ (fun x => g1 x i j) x0 :=
    fun i j => ((hg1.smooth i j).differentiable (by simp)) x0
  have hdiff2 : ∀ i j, DifferentiableAt ℝ (fun y => g2 y i j) y0 :=
    fun i j => ((hg2.smooth i j).differentiable (by simp)) y0
  have hs1 : ∀ᶠ x in 𝓝 x0, (g1 x).IsHermitian :=
    Filter.Eventually.of_forall fun x => (hg1.posDef x).isHermitian
  have hs2 : ∀ᶠ y in 𝓝 y0, (g2 y).IsHermitian :=
    Filter.Eventually.of_forall fun y => (hg2.posDef y).isHermitian
  have hrhoat : ContDiffAt ℝ 2 rho (x0,y0) :=
    (hrho.contDiffAt (hU.mem_nhds hpU)).of_le (by simp)
  rcases hTest with ⟨hell1, hell2, hsource⟩
  obtain ⟨P1, P2, K, hP1, hP2, hK, hStrict1, hStrict2, hGap⟩ :=
    ProductHessianSeparation.exists_prescribed_metric_forms_of_productHessian_positive
      g1 g2 x0 y0 rho hrhoat hdiff1 hdiff2 (hg1.posDef x0) (hg2.posDef y0)
      hs1 hs2 hell1 hell2 hsource
  obtain ⟨θ1, θ2, c, r, hSmooth1, hSmooth2, hZero1, hZero2, hFirst1, hFirst2,
      hFormula1, hFormula2, hHess1, hHess2, hPD1, hPD2, hGrad1, hGrad2,
      hUnit1, hUnit2, hc, hr, hRoom, hgap, hside⟩ :=
    OAI.AnisotropicCalderon.exists_local_product_phase_gap
      g1 g2 x0 y0 hdiff1 hdiff2 hs1 hs2 (hg1.posDef x0) (hg2.posDef y0)
      U hU hpU rho hrho hrho0 P1 P2 hP1 hP2 K hK
      hell1 hell2 hStrict1 hStrict2 hGap
  have hSrc1 : SrcStrict g1 θ1 x0 :=
    srcStrict_of_unit_metric_hessian g1 hg1 hSmooth1 x0 hGrad1 hUnit1
  have hSrc2 : SrcStrict g2 θ2 y0 :=
    srcStrict_of_unit_metric_hessian g2 hg2 hSmooth2 y0 hGrad2 hUnit2
  exact ⟨θ1, θ2, c, r, K, hSmooth1, hSmooth2, hZero1, hZero2, hFirst1, hFirst2,
    hGrad1, hGrad2, hSrc1, hSrc2, hc, hr, hK, hRoom, hgap, hside⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
