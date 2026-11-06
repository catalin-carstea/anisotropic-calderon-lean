import MixedKernelNativeProductAndBasis
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open MetricOperator MetricVolume ConnectionError
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Operator

/-- The source unit-metric Hessian condition is the exact native source strictness
for the SAME phase and the SAME admissible metric. -/
theorem srcStrict_of_unit_metric_hessian (g : MatrixField) (hg : IsAdmissibleMetric g)
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
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.posDef p).isUnit)
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
    have h := (hg.posDef p).inv.dotProduct_mulVec_pos hdθ
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
    exact metricHessianMatrix_eq_christoffelHess g hg.smooth hg.posDef hθ p i j
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

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
