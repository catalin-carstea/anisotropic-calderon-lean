import MixedKernelNativeFirstCovector
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff InnerProductSpace Topology

/-- The literal normalized Euclidean sphere defining function. -/
def normalizedSphereQuadraticModel (z : R3) : ℝ := (⟪z,z⟫_ℝ-1)/2

/-- Its exact derivative, as a function rather than only one point's jet. -/
theorem fderiv_normalizedSphereQuadraticModel :
    fderiv ℝ normalizedSphereQuadraticModel = innerSL ℝ := by
  funext z
  have hh := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.sub_const 1).const_smul ((2 : ℝ)⁻¹)
  have hfactor : (2 : ℝ)⁻¹ • (2 • innerSL ℝ z) = innerSL ℝ z := by
    rw [two_smul,smul_add,← add_smul]
    norm_num
  have hfunc : normalizedSphereQuadraticModel =
      (2 : ℝ)⁻¹ • (fun w : R3 => ‖w‖^2-1) := by
    funext w
    simp only [normalizedSphereQuadraticModel,Pi.smul_apply,smul_eq_mul,
      real_inner_self_eq_norm_sq,div_eq_mul_inv]
    ring
  rw [hfunc]
  simpa only [hfactor] using hh.fderiv

/-- The model's covariant Hessian keeps the actual connection correction. -/
theorem coordinateHessian_normalizedSphereQuadraticModel
    (Gamma : R3 → R3 → R3) (z U V : R3) :
    RadiusProfile.coordinateHessian normalizedSphereQuadraticModel Gamma z U V =
      ⟪U,V⟫_ℝ-⟪z,Gamma U V⟫_ℝ := by
  have hCD : ContDiff ℝ ∞ normalizedSphereQuadraticModel :=
    ((contDiff_id.inner ℝ contDiff_id).sub contDiff_const).div_const 2
  have hD : DifferentiableAt ℝ (fderiv ℝ normalizedSphereQuadraticModel) z :=
    (hCD.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have hFunc : (fun w => fderiv ℝ normalizedSphereQuadraticModel w V) = innerSL ℝ V := by
    funext w
    rw [fderiv_normalizedSphereQuadraticModel]
    simpa only [innerSL_apply_apply] using real_inner_comm V w
  have hEval := (hD.hasFDerivAt.clm_apply (hasFDerivAt_const V z)).fderiv
  rw [hFunc] at hEval
  have hh := congrArg (fun A : R3 →L[ℝ] ℝ => A U) hEval
  simp only [ContinuousLinearMap.fderiv,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply,
    map_zero,zero_add,innerSL_apply_apply] at hh
  have hSecond : fderiv ℝ (fderiv ℝ normalizedSphereQuadraticModel) z U V = ⟪U,V⟫_ℝ := by
    exact hh.symm.trans (real_inner_comm U V)
  unfold RadiusProfile.coordinateHessian
  rw [hSecond,fderiv_normalizedSphereQuadraticModel]
  rfl

/-- Equality of actual local scalar germs determines the full covariant Hessian. -/
theorem coordinateHessian_congr_of_eventuallyEq
    (u v : R3 → ℝ) (z : R3) (Gamma : R3 → R3 → R3)
    (hEq : u =ᶠ[𝓝 z] v) (U V : R3) :
    RadiusProfile.coordinateHessian u Gamma z U V = RadiusProfile.coordinateHessian v Gamma z U V := by
  unfold RadiusProfile.coordinateHessian
  rw [hEq.fderiv_eq,hEq.fderiv.fderiv_eq]

/-- Exact bilinearity in the two physical tangent vectors, including connection scaling. -/
theorem coordinateHessian_smul_vectors
    (u : R3 → ℝ) (Gamma : R3 →L[ℝ] R3 →L[ℝ] R3) (z : R3)
    (a b : ℝ) (U V : R3) :
    RadiusProfile.coordinateHessian u (fun X Y => Gamma X Y) z (a • U) (b • V) =
      (a*b)*RadiusProfile.coordinateHessian u (fun X Y => Gamma X Y) z U V := by
  simp only [RadiusProfile.coordinateHessian,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
