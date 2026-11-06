import Calderon.MixedKernelConstruction.MixedKernelNativeEnergyPhaseJets
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology

/-- Differentiate the SAME positive radius to rewrite its actual covariant Hessian through its logarithm. -/
theorem radius_profile_covariant_hessian_log_identity
    (r : R3 → ℝ) (hr : ContDiff ℝ ∞ r) (hpos : ∀ y : R3, 0<r y)
    (Gamma : R3 → R3 → R3) (y U V : R3) :
    r y*RadiusProfile.coordinateHessian r Gamma y U V=
      fderiv ℝ r y U*fderiv ℝ r y V+
        (r y)^2*RadiusProfile.coordinateHessian (fun Y => Real.log (r Y)) Gamma y U V := by
  let f : R3 → ℝ := fun Y => Real.log (r Y)
  have hf : ContDiff ℝ ∞ f := hr.log (fun Y => (hpos Y).ne')
  have hExp : (fun Y => Real.exp (f Y))=r := by
    funext Y
    exact Real.exp_log (hpos Y)
  have hFirst (Y W : R3) : fderiv ℝ r Y W=r Y*fderiv ℝ f Y W := by
    have hh := congrArg (fun A : R3 →L[ℝ] ℝ => A W) (fderiv_exp (hf.differentiable (by simp) Y))
    rw [hExp] at hh
    simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul,show Real.exp (f Y)=r Y from congrFun hExp Y] using hh
  have hdR : DifferentiableAt ℝ (fderiv ℝ r) y :=
    (hr.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  have hdF : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  let ev : (R3 →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ V
  have hfv := ev.hasFDerivAt.comp y hdF.hasFDerivAt
  have hModel := (hr.differentiable (by simp) y).hasFDerivAt.mul hfv
  have hNear : (fun Y : R3 => fderiv ℝ r Y V)=ᶠ[𝓝 y] (fun Y => r Y*fderiv ℝ f Y V) :=
    Filter.Eventually.of_forall (fun Y => hFirst Y V)
  have hActual := hdR.hasFDerivAt.clm_apply (hasFDerivAt_const V y)
  have hh := congrArg (fun A : R3 →L[ℝ] ℝ => A U) (hActual.unique (hModel.congr_of_eventuallyEq hNear))
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRight_apply,ev,ContinuousLinearMap.apply_apply,
    smul_eq_mul,Function.comp_def,map_zero,zero_add,add_zero] at hh
  change fderiv ℝ (fderiv ℝ r) y U V=
    r y*fderiv ℝ (fderiv ℝ f) y U V+fderiv ℝ f y V*fderiv ℝ r y U at hh
  unfold RadiusProfile.coordinateHessian
  change r y*(fderiv ℝ (fderiv ℝ r) y U V-fderiv ℝ r y (Gamma U V))=
    fderiv ℝ r y U*fderiv ℝ r y V+(r y)^2*(fderiv ℝ (fderiv ℝ f) y U V-fderiv ℝ f y (Gamma U V))
  rw [hh,hFirst y (Gamma U V),hFirst y V]
  ring

/-- The exact actual energy Hessian contains TWO profile-gradient terms and the original log-profile Hessian. -/
theorem covariant_second_nativeEnergyPhase_log_profile
    (r0 : ℝ) (rho : R3 × R3 → ℝ) (r : R3 → ℝ) (q W V : R3 × R3)
    (Gamma1 Gamma2 : R3 →L[ℝ] R3 →L[ℝ] R3)
    (hRho : ContDiffAt ℝ 2 rho q) (hr : ContDiff ℝ ∞ r) (hpos : ∀ Y : R3, 0<r Y) :
    fderiv ℝ (fderiv ℝ (nativeEnergyPhase r0 rho r)) q W V-
      fderiv ℝ (nativeEnergyPhase r0 rho r) q (Gamma1 W.1 V.1,Gamma2 W.2 V.2)=
      r0^2*(fderiv ℝ (fderiv ℝ rho) q W V-
        fderiv ℝ rho q (Gamma1 W.1 V.1,Gamma2 W.2 V.2))-
      2*fderiv ℝ r q.2 W.2*fderiv ℝ r q.2 V.2-
      (r q.2)^2*RadiusProfile.coordinateHessian (fun Y => Real.log (r Y))
        (fun A B => Gamma2 A B) q.2 W.2 V.2 := by
  rw [covariant_second_nativeEnergyPhase_apply r0 rho r q W V Gamma1 Gamma2 hRho hr,
    radius_profile_covariant_hessian_log_identity r hr hpos (fun A B => Gamma2 A B) q.2 W.2 V.2]
  ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
