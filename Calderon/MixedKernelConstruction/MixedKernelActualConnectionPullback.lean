import Calderon.MixedKernelConstruction.MixedKernelNativeJacobiBounds
import Calderon.CurvatureSkew
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator CurvatureSkew PrincipalCommutator
open scoped ContDiff InnerProductSpace Topology

/-- The ACTUAL metric pullback through the ACTUAL derivative of the coordinate map. -/
def pullbackCoordinateMetric (M : R3 → R3 →L[ℝ] R3) (f : R3 → R3) (x : R3) : R3 →L[ℝ] R3 :=
  (fderiv ℝ f x).adjoint.comp ((M (f x)).comp (fderiv ℝ f x))

/-- Smoothness requires no global invertibility of the map. -/
theorem contDiff_pullbackCoordinateMetric (M : R3 → R3 →L[ℝ] R3) (f : R3 → R3)
    (hM : ContDiff ℝ ∞ M) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pullbackCoordinateMetric M f) := by
  have hJ := hf.fderiv_right (m := ∞) (by simp)
  have hAdj : ContDiff ℝ ∞ (fun A : R3 →L[ℝ] R3 => A.adjoint) :=
    (ContinuousLinearMap.adjoint : (R3 →L[ℝ] R3) ≃ₗᵢ[ℝ] (R3 →L[ℝ] R3)).contDiff
  exact (hAdj.comp hJ).clm_comp ((hM.comp hf).clm_comp hJ)

/-- Differentiation of the actual pulled-back metric keeps both endpoint-Hessian terms. -/
theorem fderiv_pullbackCoordinateMetric_pairing
    (M : R3 → R3 →L[ℝ] R3) (f : R3 → R3)
    (hM : ContDiff ℝ ∞ M) (hf : ContDiff ℝ ∞ f) (x X U V : R3) :
    ⟪fderiv ℝ (pullbackCoordinateMetric M f) x X U,V⟫_ℝ =
      ⟪fderiv ℝ M (f x) (fderiv ℝ f x X) (fderiv ℝ f x U),fderiv ℝ f x V⟫_ℝ +
      ⟪M (f x) (fderiv ℝ (fderiv ℝ f) x X U),fderiv ℝ f x V⟫_ℝ +
      ⟪M (f x) (fderiv ℝ f x U),fderiv ℝ (fderiv ℝ f) x X V⟫_ℝ := by
  let J := fderiv ℝ f
  have hJ : ContDiff ℝ ∞ J := hf.fderiv_right (by simp)
  have hP := contDiff_pullbackCoordinateMetric M f hM hf
  have hPair : (fun y => ⟪pullbackCoordinateMetric M f y U,V⟫_ℝ) =
      fun y => ⟪M (f y) (J y U),J y V⟫_ℝ := by
    funext y
    exact ContinuousLinearMap.adjoint_inner_left (J y) V (M (f y) (J y U))
  have hEval (W : R3) : fderiv ℝ (fun y => J y W) x X = fderiv ℝ J x X W := by
    have hh := ((hJ.differentiable (by simp) x).hasFDerivAt.clm_apply (hasFDerivAt_const W x)).fderiv
    rw [hh]
    simp
  have hChain := ((hM.differentiable (by simp) (f x)).hasFDerivAt.comp x
    (hf.differentiable (by simp) x).hasFDerivAt).fderiv
  simp only [Function.comp_def] at hChain
  have hCore := directionalFDeriv_metric_pairing X (M ∘ f) (fun y => J y U) (fun y => J y V)
    (hM.comp hf) (hJ.clm_apply contDiff_const) (hJ.clm_apply contDiff_const) x
  have hLeft := directionalFDeriv_fixed_metric_pairing X U V x (pullbackCoordinateMetric M f) hP
  rw [hPair] at hLeft
  rw [← hLeft]
  simpa only [directionalFDeriv,Function.comp_def,hChain,ContinuousLinearMap.comp_apply,
    hEval,inner_add_left,J] using hCore

/-- Native Koszul and the actual metric derivative prove connection covariance at an invertible point. -/
theorem coordinateConnectionField_pullback_formula
    (M : R3 → R3 →L[ℝ] R3) (f : R3 → R3)
    (hM : ContDiff ℝ ∞ M) (hf : ContDiff ℝ ∞ f)
    (hMsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (hMpos : ∀ y U, U ≠ 0 → 0 < ⟪M y U,U⟫_ℝ)
    (hMunit : ∀ y, IsUnit (M y)) (x U V : R3) (hJ : (fderiv ℝ f x).IsInvertible) :
    let P := pullbackCoordinateMetric M f
    fderiv ℝ f x (coordinateConnectionField (inverseMetricField P) P x U V) =
      fderiv ℝ (fderiv ℝ f) x U V +
        coordinateConnectionField (inverseMetricField M) M (f x) (fderiv ℝ f x U) (fderiv ℝ f x V) := by
  intro P
  let J := fderiv ℝ f x
  let H := fderiv ℝ (fderiv ℝ f) x
  have hPair (A B : R3) : ⟪P x A,B⟫_ℝ = ⟪M (f x) (J A),J B⟫_ℝ :=
    ContinuousLinearMap.adjoint_inner_left J B (M (f x) (J A))
  have hPpos (A : R3) (hA : A ≠ 0) : 0 < ⟪P x A,A⟫_ℝ := by
    rw [hPair]
    exact hMpos (f x) (J A) (fun hz => hA (hJ.injective (by simpa using hz)))
  have hPinv : (P x).IsInvertible := by
    apply isInvertible_compactChart_endomorphism
    intro A B hab
    by_contra hne
    have hh := hPpos (A-B) (sub_ne_zero.mpr hne)
    have hz : P x (A-B) = 0 := by rw [map_sub,hab,sub_self]
    rw [hz,inner_zero_left] at hh
    linarith
  have hPunit : IsUnit (P x) := ContinuousLinearMap.isUnit_iff_bijective.mpr hPinv.bijective
  have hPi (Z : R3) : P x (inverseMetricField P x Z) = Z := by
    exact congrArg (fun A : R3 →L[ℝ] R3 => A Z) (Ring.mul_inverse_cancel (P x) hPunit)
  have hMi (Z : R3) : M (f x) (inverseMetricField M (f x) Z) = Z := by
    exact congrArg (fun A : R3 →L[ℝ] R3 => A Z) (Ring.mul_inverse_cancel (M (f x)) (hMunit (f x)))
  have hSym : ∀ A B : R3, H A B = H B A :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp)
  have hDP (A B C : R3) : ⟪fderiv ℝ P x A B,C⟫_ℝ =
      ⟪fderiv ℝ M (f x) (J A) (J B),J C⟫_ℝ +
      ⟪M (f x) (H A B),J C⟫_ℝ + ⟪M (f x) (J B),H A C⟫_ℝ :=
    fderiv_pullbackCoordinateMetric_pairing M f hM hf x A B C
  have hTest (W : R3) :
      ⟪M (f x) (J (coordinateConnectionField (inverseMetricField P) P x U V)),J W⟫_ℝ =
      ⟪M (f x) (H U V + coordinateConnectionField (inverseMetricField M) M (f x) (J U) (J V)),J W⟫_ℝ := by
    have hp := coordinateConnection_koszul (inverseMetricField P x) (P x) (fderiv ℝ P x) hPi U V W
    have hm := coordinateConnection_koszul (inverseMetricField M (f x)) (M (f x))
      (fderiv ℝ M (f x)) hMi (J U) (J V) (J W)
    rw [← coordinateConnectionField_apply (inverseMetricField P) P x U V] at hp
    rw [← coordinateConnectionField_apply (inverseMetricField M) M (f x) (J U) (J V)] at hm
    rw [hPair,hDP U V W,hDP V U W,hDP W U V,hSym V U,hSym W U,hSym W V] at hp
    have hs := hMsym (f x) (J V) (H U W)
    rw [map_add,inner_add_left]
    linarith
  have hVector : M (f x) (J (coordinateConnectionField (inverseMetricField P) P x U V)) =
      M (f x) (H U V + coordinateConnectionField (inverseMetricField M) M (f x) (J U) (J V)) := by
    apply ext_inner_right ℝ
    intro Z
    have hh := hTest (ContinuousLinearMap.inverse J Z)
    have hJI : J (ContinuousLinearMap.inverse J Z) = Z := by
      have hi := congrArg (fun A : R3 →L[ℝ] R3 => A Z) hJ.self_comp_inverse
      simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hi
    rwa [hJI] at hh
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp (hMunit (f x))).injective hVector

/-- The exact scalar second chain rule needs only local C2 regularity of the scalar. -/
theorem scalar_second_fderiv_comp_local
    (u : R3 → ℝ) (f : R3 → R3) (x U V : R3)
    (hu : ContDiffAt ℝ 2 u (f x)) (hf : ContDiff ℝ ∞ f) :
    fderiv ℝ (fderiv ℝ (u ∘ f)) x U V =
      fderiv ℝ (fderiv ℝ u) (f x) (fderiv ℝ f x U) (fderiv ℝ f x V) +
        fderiv ℝ u (f x) (fderiv ℝ (fderiv ℝ f) x U V) := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) (f x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hOuter := hdu.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt
  have hInner := hdf.hasFDerivAt.clm_apply (hasFDerivAt_const V x)
  have hModel := hOuter.clm_apply hInner
  have hNearU : ∀ᶠ y : R3 in 𝓝 x, ContDiffAt ℝ 2 u (f y) :=
    hf.continuous.continuousAt.eventually (hu.eventually (by norm_num))
  have hEq : (fun y : R3 => fderiv ℝ (u ∘ f) y V) =ᶠ[𝓝 x]
      (fun y : R3 => fderiv ℝ u (f y) (fderiv ℝ f y V)) := by
    filter_upwards [hNearU] with y hy
    exact congrArg (fun A : R3 →L[ℝ] ℝ => A V)
      (((hy.differentiableAt (by norm_num)).hasFDerivAt.comp y
        (hf.differentiable (by simp) y).hasFDerivAt).fderiv)
  have hComp : ContDiffAt ℝ 2 (u ∘ f) x := hu.comp x (hf.contDiffAt.of_le (by simp))
  have hDComp : DifferentiableAt ℝ (fderiv ℝ (u ∘ f)) x :=
    (hComp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hActual := hDComp.hasFDerivAt.clm_apply (hasFDerivAt_const V x)
  have hModel' := hModel.congr_of_eventuallyEq hEq
  have hh := congrArg (fun A : R3 →L[ℝ] ℝ => A U) (hActual.unique hModel')
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.flip_apply,map_zero,zero_add,add_zero,Function.comp_def] at hh
  change fderiv ℝ (fderiv ℝ (u ∘ f)) x U V =
      fderiv ℝ u (f x) (fderiv ℝ (fderiv ℝ f) x U V) +
        fderiv ℝ (fderiv ℝ u) (f x) (fderiv ℝ f x U) (fderiv ℝ f x V) at hh
  exact hh.trans (add_comm _ _)

/-- The actual connection correction cancels the endpoint Hessian in the scalar pullback. -/
theorem coordinateHessian_pullback_local
    (M : R3 → R3 →L[ℝ] R3) (f : R3 → R3) (u : R3 → ℝ)
    (hM : ContDiff ℝ ∞ M) (hf : ContDiff ℝ ∞ f)
    (hMsym : ∀ y U V, ⟪M y U,V⟫_ℝ = ⟪M y V,U⟫_ℝ)
    (hMpos : ∀ y U, U ≠ 0 → 0 < ⟪M y U,U⟫_ℝ)
    (hMunit : ∀ y, IsUnit (M y)) (x U V : R3) (hJ : (fderiv ℝ f x).IsInvertible)
    (hu : ContDiffAt ℝ 2 u (f x)) :
    let P := pullbackCoordinateMetric M f
    RadiusProfile.coordinateHessian (u ∘ f)
      (fun A B => coordinateConnectionField (inverseMetricField P) P x A B) x U V =
    RadiusProfile.coordinateHessian u
      (fun A B => coordinateConnectionField (inverseMetricField M) M (f x) A B)
      (f x) (fderiv ℝ f x U) (fderiv ℝ f x V) := by
  intro P
  have hConn := coordinateConnectionField_pullback_formula M f hM hf hMsym hMpos hMunit x U V hJ
  have hFirst := ((hu.differentiableAt (by norm_num)).hasFDerivAt.comp x
    (hf.differentiable (by simp) x).hasFDerivAt).fderiv
  simp only [RadiusProfile.coordinateHessian]
  rw [scalar_second_fderiv_comp_local u f x U V hu hf,hFirst]
  change _ - fderiv ℝ u (f x) (fderiv ℝ f x (coordinateConnectionField (inverseMetricField P) P x U V)) = _
  rw [hConn,map_add]
  ring

/-- Constant nonzero scaling cancels in the literal native metric connection at an invertible point. -/
theorem coordinateConnectionField_constant_smul
    (G : R3 → R3 →L[ℝ] R3) (hG : ContDiff ℝ ∞ G)
    (c : ℝ) (hc : c ≠ 0) (x U V : R3) (hInv : (G x).IsInvertible) :
    coordinateConnectionField (inverseMetricField (fun y => c • G y)) (fun y => c • G y) x U V =
      coordinateConnectionField (inverseMetricField G) G x U V := by
  have hLeft : (c • G x).comp (c⁻¹ • ContinuousLinearMap.inverse (G x)) = ContinuousLinearMap.id ℝ R3 := by
    ext Z
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_smul,smul_smul,
      hInv.self_apply_inverse,mul_inv_cancel₀ hc,inv_mul_cancel₀ hc,one_smul,ContinuousLinearMap.id_apply]
  have hRight : (c⁻¹ • ContinuousLinearMap.inverse (G x)).comp (c • G x) = ContinuousLinearMap.id ℝ R3 := by
    ext Z
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_smul,smul_smul,
      hInv.inverse_apply_self,inv_mul_cancel₀ hc,mul_inv_cancel₀ hc,one_smul,ContinuousLinearMap.id_apply]
  have hI := ContinuousLinearMap.inverse_eq hLeft hRight
  have hD : fderiv ℝ (fun y => c • G y) x = c • fderiv ℝ G x :=
    ((hG.differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv
  have hKos (D : R3 →L[ℝ] R3 →L[ℝ] R3) :
      koszulFunctional (c • D) U V = c • koszulFunctional D U V := by
    ext Z
    simp only [koszulFunctional_apply,ContinuousLinearMap.smul_apply,real_inner_smul_left,smul_eq_mul]
    ring
  simp only [coordinateConnectionField_apply,inverseMetricField]
  simp only [ContinuousLinearMap.ringInverse_eq_inverse]
  rw [hI,hD]
  unfold coordinateConnection
  rw [hKos]
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_smul,inv_mul_cancel₀ hc,mul_inv_cancel₀ hc,mul_one]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
