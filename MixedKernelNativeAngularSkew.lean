import MixedKernelParallelAngularTangency
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError MetricOperator
open scoped InnerProductSpace

/-- The literal parallel angular velocity, packaged as its actual linear operator in z. -/
def framedParallelAngularOperator (F : R3 → R3 →L[ℝ] R3)
    (Gamma : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (y X : R3) : R3 →L[ℝ] R3 :=
  -(ContinuousLinearMap.inverse (F y)).comp (fderiv ℝ F y X+(Gamma y X).comp (F y))

/-- This is exactly the existing native angular velocity, with the same negative sign. -/
theorem framedParallelAngularOperator_apply
    (F : R3 → R3 →L[ℝ] R3) (Gamma : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (y X z : R3) :
    framedParallelAngularOperator F Gamma y X z = framedParallelAngularVelocity F Gamma y X z := rfl

/-- Polarization of a real linear zero quadratic form gives the exact skew identity. -/
theorem continuousLinearMap_skew_of_quadratic_zero
    (A : R3 →L[ℝ] R3) (hA : ∀ z : R3, ⟪A z,z⟫_ℝ = 0) (U V : R3) :
    ⟪A U,V⟫_ℝ = -⟪U,A V⟫_ℝ := by
  have hh := hA (U+V)
  simp only [map_add,inner_add_left,inner_add_right,hA U,hA V,zero_add,add_zero] at hh
  rw [real_inner_comm U (A V)] at hh
  linarith

/-- The SAME native conformal frame/connection have exactly skew angular velocity. -/
theorem native_parallelAngularVelocity_skew
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (y X U V : R3) :
    let F : R3 → R3 →L[ℝ] R3 := fun u => conformalReferenceGramFrameOperatorJoint g L (lam,u)
    let Gamma := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L lam)))
      (metricOperatorField (conformalReferenceMatrix g L lam))
    ⟪framedParallelAngularVelocity F Gamma y X U,V⟫_ℝ =
      -⟪U,framedParallelAngularVelocity F Gamma y X V⟫_ℝ := by
  intro F Gamma
  have hzero (z : R3) : ⟪framedParallelAngularOperator F Gamma y X z,z⟫_ℝ = 0 := by
    rw [framedParallelAngularOperator_apply]
    exact native_parallelAngularVelocity_inner_eq_zero g hg L lam y X z
  simpa only [framedParallelAngularOperator_apply] using
    continuousLinearMap_skew_of_quadratic_zero (framedParallelAngularOperator F Gamma y X) hzero U V

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
