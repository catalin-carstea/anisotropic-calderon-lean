import Calderon.ActualFrameParallelVelocity
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError MetricOperator NormalCoordinatesFrame CurvatureSkew PrincipalCommutator
open scoped ContDiff InnerProductSpace

/-- Actual metric compatibility makes the literal parallel angular velocity tangent. -/
theorem framedParallelAngularVelocity_inner_eq_zero
    (M : R3 → R3 →L[ℝ] R3) (Gamma : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hF : ContDiff ℝ ∞ (fun y => frameOperator (e y)))
    (he : ∀ y, IsMetricOrthonormalFrame (M y) (e y))
    (hsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (hcomp : ∀ y X U V, ⟪M y (Gamma y X U),V⟫_ℝ + ⟪M y U,Gamma y X V⟫_ℝ =
      ⟪fderiv ℝ M y X U,V⟫_ℝ) (y X z : R3) :
    ⟪framedParallelAngularVelocity (fun u => frameOperator (e u)) Gamma y X z,z⟫_ℝ = 0 := by
  let F : R3 → R3 →L[ℝ] R3 := fun u => frameOperator (e u)
  have hFz : ContDiff ℝ ∞ (fun u => F u z) := hF.clm_apply contDiff_const
  have hDF : fderiv ℝ (fun u => F u z) y X = fderiv ℝ F y X z := by
    have hh := ((hF.differentiable (by simp) y).hasFDerivAt.clm_apply
      (hasFDerivAt_const z y)).fderiv
    rw [hh]
    simp [F]
  have hconstant : (fun u => ⟪M u (F u z),F u z⟫_ℝ) = fun _ : R3 => ⟪z,z⟫_ℝ := by
    funext u
    exact metric_inner_frameOperator (M u) (e u) (he u) z z
  have hd := directionalFDeriv_metric_pairing X M (fun u => F u z) (fun u => F u z) hM hFz hFz y
  rw [hconstant] at hd
  simp only [directionalFDeriv,fderiv_const_apply,zero_apply,hDF] at hd
  have hc := hcomp y X (F y z) (F y z)
  have hs1 := hsym y (F y z) (fderiv ℝ F y X z)
  have hs2 := hsym y (F y z) (Gamma y X (F y z))
  have hB : ⟪M y (fderiv ℝ F y X z + Gamma y X (F y z)),F y z⟫_ℝ = 0 := by
    simp only [inner_add_left] at hd
    simp only [map_add,inner_add_left]
    linarith
  have hInv : (F y).IsInvertible :=
    isInvertible_compactChart_endomorphism _ (frameOperator_injective _ _ (he y))
  have hp := metric_inner_frameOperator (M y) (e y) (he y)
    (framedParallelAngularVelocity F Gamma y X z) z
  rw [frame_apply_parallelAngularVelocity F Gamma y X z hInv] at hp
  simp only [map_neg,inner_neg_left] at hp
  change -⟪M y (fderiv ℝ F y X z + Gamma y X (F y z)),F y z⟫_ℝ =
    ⟪framedParallelAngularVelocity F Gamma y X z,z⟫_ℝ at hp
  rw [hB,neg_zero] at hp
  exact hp.symm

/-- The SAME native conformal Gram frame and coordinate connection satisfy this tangency. -/
theorem native_parallelAngularVelocity_inner_eq_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (y X z : R3) :
    let F : R3 → R3 →L[ℝ] R3 := fun u => conformalReferenceGramFrameOperatorJoint g L (lam,u)
    let Gamma := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L lam)))
      (metricOperatorField (conformalReferenceMatrix g L lam))
    ⟪framedParallelAngularVelocity F Gamma y X z,z⟫_ℝ = 0 := by
  intro F Gamma
  let M := metricOperatorField (conformalReferenceMatrix g L lam)
  let e : R3 → Fin 3 → R3 := fun u => NormalCoordinatesFrame.metricGramFrame (M u)
  obtain ⟨hM,_,hsym,hpos,hMQ⟩ := conformalReference_slice_data g hg L lam
  have hFraw := (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp
    (show ContDiff ℝ ∞ (fun u : R3 => (lam,u)) from contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ (fun u => frameOperator (e u)) := by
    simpa only [Function.comp_def,conformalReferenceGramFrameOperatorJoint,e,M,
      conformalReferenceOperatorJoint] using hFraw
  have he (u : R3) : IsMetricOrthonormalFrame (M u) (e u) :=
    NormalCoordinatesFrame.metricGramFrame_isMetricOrthonormalFrame (M u) (hsym u) (hpos u)
  change ⟪framedParallelAngularVelocity (fun u => frameOperator (e u)) Gamma y X z,z⟫_ℝ = 0
  exact framedParallelAngularVelocity_inner_eq_zero M Gamma e hM hF he hsym
    (coordinateConnectionField_metric_compatible (inverseMetricField M) M hM hsym hMQ) y X z

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
