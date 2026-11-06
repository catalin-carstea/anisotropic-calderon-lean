import Calderon.MixedKernelConstruction.MixedKernelProductPhases
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open MetricOperator MetricVolume ConnectionError
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Operator

theorem srcStrict_of_unit_metric_hessian_smooth (g : MatrixField)
    (hsmooth : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) (hpos : ∀ x, (g x).PosDef)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3)
    (hdθ : (fun k => pd k θ p) ≠ 0)
    (hunit :
      let b : R3 := matrixOperatorMap ((g p)⁻¹) (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))
      let e : R3 := (Real.sqrt ⟪metricOperatorField g p b, b⟫_ℝ)⁻¹ • b
      ∀ v : R3, ⟪metricOperatorField g p v, e⟫_ℝ = 0 →
        ⟪metricOperatorField g p v, v⟫_ℝ = 1 →
        0 < RadiusProfile.coordinateHessian θ
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) p X Y) p e e +
          RadiusProfile.coordinateHessian θ
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) p X Y) p v v) :
    SrcStrict g θ p := by
  let M : R3 →L[ℝ] R3 := metricOperatorField g p
  let b : R3 := matrixOperatorMap ((g p)⁻¹) (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))
  let n : ℝ := ⟪M b,b⟫_ℝ
  let t : ℝ := (Real.sqrt n)⁻¹
  let e : R3 := t • b
  let Γ : R3 →L[ℝ] R3 →L[ℝ] R3 := coordinateConnectionField
    (inverseMetricField (metricOperatorField g)) (metricOperatorField g) p
  let H : R3 →L[ℝ] R3 →L[ℝ] ℝ := coordinateHessianBilinear θ Γ p
  have hGA : ∀ U : R3, M (matrixOperatorMap ((g p)⁻¹) U) = U := by
    have hmat : g p * (g p)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hpos p).isUnit)
    have hop : matrixOperatorMap (g p) * matrixOperatorMap ((g p)⁻¹) = 1 := by
      change matrixOperatorAlgEquiv (g p) * matrixOperatorAlgEquiv ((g p)⁻¹) = 1
      rw [← map_mul, hmat, map_one]
    intro U
    change (matrixOperatorMap (g p) * matrixOperatorMap ((g p)⁻¹)) U = U
    rw [hop]
    rfl
  have hn : 0 < n := by
    change 0 < ⟪M (matrixOperatorMap ((g p)⁻¹)
      (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))),
      matrixOperatorMap ((g p)⁻¹) (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))⟫_ℝ
    rw [hGA]
    have h := (hpos p).inv.dotProduct_mulVec_pos hdθ
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec, matrixOperator_coordinate,
      PiLp.toLp_apply, mul_comm, OAI.AnisotropicCalderon.grad] using h
  have hnN : n = StrictWeightCarleman.phaseNorm (fun i j y => (g y)⁻¹ i j) θ p := by
    change ⟪M (matrixOperatorMap ((g p)⁻¹)
      (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))),
      matrixOperatorMap ((g p)⁻¹) (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))⟫_ℝ = _
    rw [hGA]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec, matrixOperator_coordinate,
      PiLp.toLp_apply, StrictWeightCarleman.phaseNorm, OAI.AnisotropicCalderon.grad,
      Fin.sum_univ_three]
    ring
  have hbc (i : Fin 3) : b i = StrictWeightCarleman.phaseField
      (fun i j y => (g y)⁻¹ i j) θ i p := rfl
  have hmetric (X Y : R3) : ⟪M X,Y⟫_ℝ = ∑ i : Fin 3, ∑ j : Fin 3,
      g p i j * Y i * X j := by
    change ⟪(g p).toEuclideanLin X,Y⟫_ℝ = _
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply, star_trivial,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  have hHentry (i j : Fin 3) : H (coordinateVector i) (coordinateVector j) =
      StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i j y => (g y)⁻¹ i j) θ p i j := by
    rw [show H = coordinateHessianBilinear θ Γ p from rfl,
      coordinateHessianBilinear_apply]
    change metricHessianMatrix g θ p i j = _
    exact metricHessianMatrix_eq_christoffelHess g hsmooth hpos hθ p i j
  have hHquad (X : R3) : H X X = ∑ i : Fin 3, ∑ j : Fin 3,
      StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i j y => (g y)⁻¹ i j) θ p i j * X i * X j := by
    rw [bilinear_coordinate_sum H X X]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hHentry]
    ring
  have ht2 : t ^ 2 = 1 / n := by simp only [t, inv_pow, Real.sq_sqrt hn.le, one_div]
  have hHE : H e e = H b b / n := by
    calc H e e = t ^ 2 * H b b := by
          simp only [e, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
          ring
      _ = (1 / n) * H b b := by rw [ht2]
      _ = H b b / n := by ring
  change ∀ v : Fin 3 → ℝ, _ → _ → _
  intro v hv horth
  let V : R3 := WithLp.toLp 2 v
  have hVnorm : ⟪M V,V⟫_ℝ = 1 := by simpa only [hmetric, V, PiLp.toLp_apply] using hv
  have hVorth : ⟪M V,e⟫_ℝ = 0 := by
    have hborth : ⟪M V,b⟫_ℝ = 0 := by
      simpa only [hmetric, hbc, V, PiLp.toLp_apply] using horth
    change ⟪M V,t • b⟫_ℝ = 0
    rw [inner_smul_right, hborth, mul_zero]
  have hpos : 0 < H e e + H V V := hunit V hVorth hVnorm
  rw [hHE] at hpos
  change 0 < srcFun g θ p v
  unfold srcFun
  have hbval : (∑ i : Fin 3, ∑ j : Fin 3,
      StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i j y => (g y)⁻¹ i j) θ p i j *
      StrictWeightCarleman.phaseField (fun i j y => (g y)⁻¹ i j) θ i p *
      StrictWeightCarleman.phaseField (fun i j y => (g y)⁻¹ i j) θ j p) = H b b := by
    simpa only [hbc] using (hHquad b).symm
  have hvval : (∑ i : Fin 3, ∑ j : Fin 3,
      StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i j y => (g y)⁻¹ i j) θ p i j * v i * v j) = H V V := by
    simpa only [V, PiLp.toLp_apply] using (hHquad V).symm
  rw [hbval, hvval, ← hnN]
  exact hpos

theorem exists_native_product_strict_phases_smooth
    (g1 g2 : MatrixField)
    (hsmooth1 : ∀ i j, ContDiff ℝ ∞ (fun x => g1 x i j)) (hpos1 : ∀ x, (g1 x).PosDef)
    (hsmooth2 : ∀ i j, ContDiff ℝ ∞ (fun y => g2 y i j)) (hpos2 : ∀ y, (g2 y).PosDef)
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
    fun i j => ((hsmooth1 i j).differentiable (by simp)) x0
  have hdiff2 : ∀ i j, DifferentiableAt ℝ (fun y => g2 y i j) y0 :=
    fun i j => ((hsmooth2 i j).differentiable (by simp)) y0
  have hs1 : ∀ᶠ x in 𝓝 x0, (g1 x).IsHermitian :=
    Filter.Eventually.of_forall fun x => (hpos1 x).isHermitian
  have hs2 : ∀ᶠ y in 𝓝 y0, (g2 y).IsHermitian :=
    Filter.Eventually.of_forall fun y => (hpos2 y).isHermitian
  have hrhoat : ContDiffAt ℝ 2 rho (x0,y0) :=
    (hrho.contDiffAt (hU.mem_nhds hpU)).of_le (by simp)
  rcases hTest with ⟨hell1, hell2, hsource⟩
  obtain ⟨P1, P2, K, hP1, hP2, hK, hStrict1, hStrict2, hGap⟩ :=
    ProductHessianSeparation.exists_prescribed_metric_forms_of_productHessian_positive
      g1 g2 x0 y0 rho hrhoat hdiff1 hdiff2 (hpos1 x0) (hpos2 y0)
      hs1 hs2 hell1 hell2 hsource
  obtain ⟨θ1, θ2, c, r, hSmooth1, hSmooth2, hZero1, hZero2, hFirst1, hFirst2,
      hFormula1, hFormula2, hHess1, hHess2, hPD1, hPD2, hGrad1, hGrad2,
      hUnit1, hUnit2, hc, hr, hRoom, hgap, hside⟩ :=
    OAI.AnisotropicCalderon.exists_local_product_phase_gap
      g1 g2 x0 y0 hdiff1 hdiff2 hs1 hs2 (hpos1 x0) (hpos2 y0)
      U hU hpU rho hrho hrho0 P1 P2 hP1 hP2 K hK
      hell1 hell2 hStrict1 hStrict2 hGap
  have hSrc1 : SrcStrict g1 θ1 x0 :=
    srcStrict_of_unit_metric_hessian_smooth g1 hsmooth1 hpos1 hSmooth1 x0 hGrad1 hUnit1
  have hSrc2 : SrcStrict g2 θ2 y0 :=
    srcStrict_of_unit_metric_hessian_smooth g2 hsmooth2 hpos2 hSmooth2 y0 hGrad2 hUnit2
  exact ⟨θ1, θ2, c, r, K, hSmooth1, hSmooth2, hZero1, hZero2, hFirst1, hFirst2,
    hGrad1, hGrad2, hSrc1, hSrc2, hc, hr, hK, hRoom, hgap, hside⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
