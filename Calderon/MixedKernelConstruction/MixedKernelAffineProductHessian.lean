import Calderon.MixedKernelConstruction.MixedKernelNativeQuadraticModel
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError
open scoped ContDiff Topology

/-- The exact second derivative of a scalar function along a fixed genuine affine map. -/
theorem scalar_second_fderiv_affine_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : F → ℝ) (A : E →L[ℝ] F) (b : F) (x U V : E)
    (hu : ContDiffAt ℝ 2 u (b+A x)) :
    fderiv ℝ (fderiv ℝ (fun X => u (b+A X))) x U V =
      fderiv ℝ (fderiv ℝ u) (b+A x) (A U) (A V) := by
  let f : E → F := fun X => b+A X
  have hf : ContDiff ℝ ∞ f := contDiff_const.add A.contDiff
  have hdf (X : E) : HasFDerivAt f A X := A.hasFDerivAt.const_add b
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (f x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hOuter := hdu.hasFDerivAt.comp x (hdf x)
  have hModel := hOuter.clm_apply (hasFDerivAt_const (A V) x)
  have hNear : ∀ᶠ X in 𝓝 x, ContDiffAt ℝ 2 u (f X) :=
    hf.continuous.continuousAt.eventually (hu.eventually (by norm_num))
  have hEq : (fun X : E => fderiv ℝ (fun Y => u (f Y)) X V) =ᶠ[𝓝 x]
      (fun X => fderiv ℝ u (f X) (A V)) := by
    filter_upwards [hNear] with X hX
    exact congrArg (fun B : E →L[ℝ] ℝ => B V)
      (((hX.differentiableAt (by norm_num)).hasFDerivAt.comp X (hdf X)).fderiv)
  have hComp : ContDiffAt ℝ 2 (fun X => u (f X)) x := hu.comp x (hf.contDiffAt.of_le (by simp))
  have hDComp : DifferentiableAt ℝ (fderiv ℝ (fun X => u (f X))) x :=
    (hComp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hActual := hDComp.hasFDerivAt.clm_apply (hasFDerivAt_const V x)
  have hModel' := hModel.congr_of_eventuallyEq hEq
  have hh := congrArg (fun B : E →L[ℝ] ℝ => B U) (hActual.unique hModel')
  simpa only [Function.comp_def,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.flip_apply,map_zero,zero_add,add_zero,f] using hh

/-- The actual slice derivatives are the literal full-product xx derivatives. -/
theorem fst_slice_derivatives_eq_product
    (rho : R3 × R3 → ℝ) (x y U V : R3) (hRho : ContDiffAt ℝ 2 rho (x,y)) :
    (fderiv ℝ (fun X => rho (X,y)) x U=fderiv ℝ rho (x,y) (U,0)) ∧
    (fderiv ℝ (fderiv ℝ (fun X => rho (X,y))) x U V=
      fderiv ℝ (fderiv ℝ rho) (x,y) (U,0) (V,0)) := by
  have hD := ((hRho.differentiableAt (by norm_num)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x))).fderiv
  simp only [Function.comp_def,id_eq] at hD
  constructor
  · rw [hD]
    rfl
  · have hPoint : ((0 : R3),y)+(ContinuousLinearMap.inl ℝ R3 R3) x=(x,y) := by simp
    have hAffine := scalar_second_fderiv_affine_pullback rho (ContinuousLinearMap.inl ℝ R3 R3)
      ((0 : R3),y) x U V (by simpa only [hPoint] using hRho)
    simpa only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero] using hAffine

/-- The actual partial coordinate Hessian is exactly its full-product xx block. -/
theorem coordinateHessian_fst_slice_eq_product
    (rho : R3 × R3 → ℝ) (x y U V : R3)
    (Gamma : R3 →L[ℝ] R3 →L[ℝ] R3) (hRho : ContDiffAt ℝ 2 rho (x,y)) :
    RadiusProfile.coordinateHessian (fun X => rho (X,y)) (fun A B => Gamma A B) x U V=
      fderiv ℝ (fderiv ℝ rho) (x,y) (U,0) (V,0)-fderiv ℝ rho (x,y) (Gamma U V,0) := by
  unfold RadiusProfile.coordinateHessian
  rw [(fst_slice_derivatives_eq_product rho x y U V hRho).2,
    (fst_slice_derivatives_eq_product rho x y (Gamma U V) V hRho).1]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
