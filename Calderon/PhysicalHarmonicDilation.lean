import Calderon.MetricPullbackDivergence
import Calderon.ActualNearBallHarmonicLift
/-! Dilation of the metric harmonic data. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Gradient InnerProductSpace Matrix Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator NormalCoordinatesFrame

theorem pullbackMetric_dilation
    (g : MatrixField) (q : ℝ) (x : R3) :
    pullbackMetric g (fun y : R3 => q • y) x = q^2 • g (q • x) := by
  have hD : HasFDerivAt (fun y : R3 => q • y) (q • ContinuousLinearMap.id ℝ R3) x :=
    (q • ContinuousLinearMap.id ℝ R3).hasFDerivAt
  have hId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) = (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
    matrixOperatorAlgEquiv.symm.map_one
  have hQ : operatorMatrixMap (q • ContinuousLinearMap.id ℝ R3) =
      q • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by rw [map_smul,hId]
  simp only [pullbackMetric,hD.fderiv,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
    operatorMatrixMap_metricOperatorField,hQ,Matrix.transpose_smul,Matrix.transpose_one,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul,pow_two]


theorem principalCoefficient_pullbackMetric_dilation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (q : ℝ) (hq : q ≠ 0) (x : R3) :
    principalCoefficient (pullbackMetric g (fun y : R3 => q • y)) x =
      |q| • principalCoefficient (fun y : R3 => g (q • y)) x := by
  have hExp : Real.exp (2 * Real.log |q|) = q^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log (abs_pos.mpr hq),← pow_two,sq_abs]
  have hMetric : pullbackMetric g (fun y : R3 => q • y) =
      conformalMatrix (fun y : R3 => g (q • y)) (fun _ : R3 => Real.log |q|) := by
    funext y
    rw [pullbackMetric_dilation]
    simp only [conformalMatrix,hExp]
  rw [hMetric,principalCoefficient_conformalMatrix _ _ (fun y => hg.posDef (q • y)) x,
    Real.exp_log (abs_pos.mpr hq)]


theorem coordinateFluxDivergence_metricDivergenceFlux_dilation
    (g : MatrixField) (hg : IsAdmissibleMetric g) (q : ℝ) (u : SmoothData) (x : R3) :
    coordinateFluxDivergence
      (metricDivergenceFlux (fun y : R3 => g (q • y)) (fun y : R3 => u.1 (q • y))) x =
      q^2 * coordinateFluxDivergence (metricDivergenceFlux g u.1) (q • x) := by
  by_cases hq : q = 0
  · subst q
    simp only [zero_smul,zero_pow,zero_mul]
    simp [coordinateFluxDivergence,metricDivergenceFlux,gradient_fun_const]
  · let D : R3 → R3 := fun y => q • y
    let Z := metricDivergenceFlux (fun y : R3 => g (q • y)) (u.1 ∘ D)
    have hD : ContDiff ℝ ∞ D := (q • ContinuousLinearMap.id ℝ R3).contDiff
    have hDX (y : R3) : HasFDerivAt D (q • ContinuousLinearMap.id ℝ R3) y :=
      (q • ContinuousLinearMap.id ℝ R3).hasFDerivAt
    have hId : operatorMatrixMap (ContinuousLinearMap.id ℝ R3) = (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      matrixOperatorAlgEquiv.symm.map_one
    have hJac : coordinateJacobianMatrix D x = q • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [coordinateJacobianMatrix_eq_operatorMatrixMap,(hDX x).fderiv,map_smul,hId]
    have hJ : IsUnit (coordinateJacobianMatrix D x).det := by
      apply isUnit_iff_ne_zero.mpr
      rw [hJac,Matrix.det_smul,Fintype.card_fin,Matrix.det_one,mul_one]
      exact pow_ne_zero 3 hq
    have hDet : |(coordinateJacobianMatrix D x).det| = |q|^3 := by
      rw [hJac,Matrix.det_smul,Fintype.card_fin,Matrix.det_one,mul_one,abs_pow]
    have hZ : ContDiff ℝ ∞ Z := contDiff_metricDivergenceFlux
      (fun y : R3 => g (q • y))
      (fun i j => (hg.smooth i j).comp hD) (fun y => hg.posDef (q • y))
      (u.1 ∘ D) (u.2.comp hD)
    have hFlux : metricDivergenceFlux (pullbackMetric g D) (u.1 ∘ D) =
        fun y => |q| • Z y := by
      funext y
      have hCoeff : principalCoefficient (pullbackMetric g D) y =
          |q| • principalCoefficient (fun y : R3 => g (q • y)) y :=
        principalCoefficient_pullbackMetric_dilation g hg q hq y
      simp only [metricDivergenceFlux,hCoeff,map_smul,smul_apply,Z]
    have hScale : coordinateFluxDivergence (fun y => |q| • Z y) x =
        |q| * coordinateFluxDivergence Z x := by
      have hc := coordinateFluxDivergence_exp_depth (fun _ : R3 => Real.log |q|)
        Z (-1) x (differentiableAt_const _) (hZ.differentiable (by simp) x)
      simpa only [neg_neg,one_mul,Real.exp_log (abs_pos.mpr hq),fderiv_const_apply,
        zero_apply,mul_zero,sub_zero] using hc
    have hCov := coordinateFluxDivergence_metricDivergenceFlux_pullbackMetric
      g hg.smooth hg.posDef D u.1 hD u.2 x hJ
    rw [hFlux,hScale,hDet] at hCov
    apply mul_left_cancel₀ (abs_pos.mpr hq).ne'
    calc
      _ = |q|^3 * coordinateFluxDivergence (metricDivergenceFlux g u.1) (q • x) := hCov
      _ = _ := by rw [← sq_abs q]; ring


theorem coordinateFluxDivergence_metricDivergenceFlux_dilation_of_contDiffOn
    (g : MatrixField) (hg : IsAdmissibleMetric g) (q : ℝ)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (x : R3) (hx : q • x ∈ S) :
    coordinateFluxDivergence
      (metricDivergenceFlux (fun y : R3 => g (q • y)) (fun y : R3 => u (q • y))) x =
      q^2 * coordinateFluxDivergence (metricDivergenceFlux g u) (q • x) := by
  have hCover : ({q • x} : Set R3) ⊆ S := by
    intro y hy
    rw [mem_singleton_iff] at hy
    simpa only [hy] using hx
  obtain ⟨v,_,hNear⟩ := DirichletFamily.exists_smoothData_eq_near_compact
    ({q • x} : Set R3) S isCompact_singleton hS hCover u hu
  have hvu : v.1 =ᶠ[𝓝 (q • x)] u := hNear (q • x) (mem_singleton (q • x))
  have hvuq : (fun y : R3 => v.1 (q • y)) =ᶠ[𝓝 x] (fun y : R3 => u (q • y)) :=
    (q • ContinuousLinearMap.id ℝ R3).continuous.continuousAt.tendsto.eventually hvu
  calc
    _ = coordinateFluxDivergence
        (metricDivergenceFlux (fun y : R3 => g (q • y)) (fun y : R3 => v.1 (q • y))) x :=
      (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
        (fun y : R3 => g (q • y)) (fun y : R3 => v.1 (q • y))
          (fun y : R3 => u (q • y)) x hvuq).symm
    _ = q^2 * coordinateFluxDivergence (metricDivergenceFlux g v.1) (q • x) :=
      coordinateFluxDivergence_metricDivergenceFlux_dilation g hg q v x
    _ = _ := congrArg (fun c : ℝ => q^2 * c)
      (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq g v.1 u (q • x) hvu)

end OAI.AnisotropicCalderon.ConnectionError
