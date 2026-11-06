import Calderon.MetricPullbackFlux

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.NativeSourceChartCalculus
open ConnectionError MetricOperator

lemma pullbackMetric_posDef_of_injective_fderiv
    (g : MatrixField) (hg : IsAdmissibleMetric g) (X : R3 → R3) (x : R3)
    (hDX : Function.Injective (fderiv ℝ X x)) : (pullbackMetric g X x).PosDef := by
  let B : R3 →L[ℝ] R3 := fderiv ℝ X x
  let M : R3 →L[ℝ] R3 := metricOperatorField g (X x)
  change (operatorMatrixMap (B.adjoint.comp (M.comp B))).PosDef
  apply operatorMatrixMap_posDef
  · intro u v
    change inner ℝ (B.adjoint (M (B u))) v = inner ℝ (B.adjoint (M (B v))) u
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    exact metricOperatorField_symmetric g hg (X x) (B u) (B v)
  · intro u hu
    have hBu : B u ≠ 0 := by
      intro hz
      apply hu
      apply hDX
      simpa only [map_zero] using hz
    change 0 < inner ℝ (B.adjoint (M (B u))) u
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact metricOperatorField_pos g hg (X x) (B u) hBu

end OAI.AnisotropicCalderon.NativeSourceChartCalculus
