import Calderon.MetricPullbackFlux

set_option autoImplicit false
noncomputable section
open Filter Function
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator

theorem coordinateJacobianMatrix_comp_of_differentiableAt
    (F X : R3 → R3) (x : R3) (hF : DifferentiableAt ℝ F (X x))
    (hX : DifferentiableAt ℝ X x) :
    coordinateJacobianMatrix (F ∘ X) x =
      coordinateJacobianMatrix F (X x) * coordinateJacobianMatrix X x := by
  rw [coordinateJacobianMatrix_eq_operatorMatrixMap,
    fderiv_comp x hF hX,operatorMatrixMap_comp,
    ← coordinateJacobianMatrix_eq_operatorMatrixMap,
    ← coordinateJacobianMatrix_eq_operatorMatrixMap]

theorem pullbackMetric_eq_coordinate_form (g : MatrixField) (X : R3 → R3) (x : R3) :
    pullbackMetric g X x = (coordinateJacobianMatrix X x).transpose * g (X x) *
      coordinateJacobianMatrix X x := by
  simp only [pullbackMetric,operatorMatrixMap_comp,operatorMatrixMap_adjoint,
    operatorMatrixMap_metricOperatorField,coordinateJacobianMatrix_eq_operatorMatrixMap,
    Matrix.mul_assoc]

theorem pullbackMetric_comp_of_differentiableAt
    (g : MatrixField) (F X : R3 → R3) (x : R3) (hF : DifferentiableAt ℝ F (X x))
    (hX : DifferentiableAt ℝ X x) :
    pullbackMetric g (F ∘ X) x = pullbackMetric (pullbackMetric g F) X x := by
  rw [pullbackMetric_eq_coordinate_form,pullbackMetric_eq_coordinate_form,
    pullbackMetric_eq_coordinate_form,coordinateJacobianMatrix_comp_of_differentiableAt F X x hF hX]
  simp only [Function.comp_apply,Matrix.transpose_mul,Matrix.mul_assoc]

theorem pullbackMetric_const_smul
    (g : MatrixField) (c : ℝ) (X : R3 → R3) (x : R3) :
    pullbackMetric (fun z => c • g z) X x = c • pullbackMetric g X x := by
  rw [pullbackMetric_eq_coordinate_form,pullbackMetric_eq_coordinate_form]
  simp only [Matrix.mul_smul,Matrix.smul_mul]

theorem pullbackMetric_eventuallyEq_of_eventuallyEq
    (g : MatrixField) (F X : R3 → R3) (x : R3) (h : F =ᶠ[𝓝 x] X) :
    pullbackMetric g F =ᶠ[𝓝 x] pullbackMetric g X := by
  filter_upwards [h,h.fderiv (𝕜 := ℝ)] with z hz hDz
  simp only [pullbackMetric,hz,hDz]

end OAI.AnisotropicCalderon.ConnectionError
