import Calderon.MixedKernelConstruction.MixedKernelNativeConstantRadiusPhase
import Calderon.MetricHessianQuadratic
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator
open scoped ContDiff Topology

/-- The exact energy phase for the same native moving spheres. -/
def nativeEnergyPhase (r0 : ℝ) (rho : R3 × R3 → ℝ) (r : R3 → ℝ) : R3 × R3 → ℝ :=
  fun a => r0^2*(rho a+1/2)-(r a.2)^2/2

/-- The profile term is subtracted in the genuine first derivative. -/
theorem fderiv_nativeEnergyPhase_apply
    (r0 : ℝ) (rho : R3 × R3 → ℝ) (r : R3 → ℝ) (q W : R3 × R3)
    (hRho : DifferentiableAt ℝ rho q) (hr : DifferentiableAt ℝ r q.2) :
    fderiv ℝ (nativeEnergyPhase r0 rho r) q W =
      r0^2*fderiv ℝ rho q W-r q.2*fderiv ℝ r q.2 W.2 := by
  have hRR := hr.hasFDerivAt.comp q (hasFDerivAt_snd (𝕜 := ℝ) (p := q))
  have hF := ((hRho.hasFDerivAt.add_const (1/2 : ℝ)).const_smul (r0^2)).sub
    ((hRR.mul hRR).const_smul (1/2 : ℝ))
  have heq : (fun a : R3 × R3 => r0^2 • (rho a+1/2)-(1/2 : ℝ) • (r a.2*r a.2))=nativeEnergyPhase r0 rho r := by
    funext a
    simp only [nativeEnergyPhase,smul_eq_mul,pow_two]
    ring
  change HasFDerivAt (fun a : R3 × R3 => r0^2 • (rho a+1/2)-(1/2 : ℝ) • (r a.2*r a.2)) _ q at hF
  rw [heq] at hF
  rw [hF.fderiv]
  change r0^2*fderiv ℝ rho q W-(1/2 : ℝ)*(r q.2*fderiv ℝ r q.2 W.2+r q.2*fderiv ℝ r q.2 W.2)=_
  ring

/-- Smoothness of the SAME energy phase on an actual C2 phase neighborhood. -/
theorem contDiffAt_nativeEnergyPhase
    (r0 : ℝ) (rho : R3 × R3 → ℝ) (r : R3 → ℝ) (q : R3 × R3)
    (hRho : ContDiffAt ℝ 2 rho q) (hr : ContDiff ℝ ∞ r) :
    ContDiffAt ℝ 2 (nativeEnergyPhase r0 rho r) q := by
  exact ((hRho.add contDiffAt_const).const_smul (r0^2)).sub
    (((hr.comp contDiff_snd).contDiffAt.of_le (by simp)).pow 2 |>.div_const 2)

/-- Differentiate the first-jet identity on a neighborhood, retaining BOTH profile terms. -/
theorem second_fderiv_nativeEnergyPhase_apply
    (r0 : ℝ) (rho : R3 × R3 → ℝ) (r : R3 → ℝ) (q W V : R3 × R3)
    (hRho : ContDiffAt ℝ 2 rho q) (hr : ContDiff ℝ ∞ r) :
    fderiv ℝ (fderiv ℝ (nativeEnergyPhase r0 rho r)) q W V =
      r0^2*fderiv ℝ (fderiv ℝ rho) q W V-
        (fderiv ℝ r q.2 W.2*fderiv ℝ r q.2 V.2+
          r q.2*fderiv ℝ (fderiv ℝ r) q.2 W.2 V.2) := by
  have hdRho : DifferentiableAt ℝ (fderiv ℝ rho) q :=
    (hRho.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdR : DifferentiableAt ℝ (fderiv ℝ r) q.2 :=
    (hr.fderiv_right (m := ∞) (by simp)).differentiable (by simp) q.2
  let ev : ((R3 × R3) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ V
  let evR : (R3 →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ V.2
  have hRhoV := ev.hasFDerivAt.comp q hdRho.hasFDerivAt
  have hRV := (evR.hasFDerivAt.comp q.2 hdR.hasFDerivAt).comp q
    (hasFDerivAt_snd (𝕜 := ℝ) (p := q))
  have hR := (hr.differentiable (by simp) q.2).hasFDerivAt.comp q
    (hasFDerivAt_snd (𝕜 := ℝ) (p := q))
  have hModel := (hRhoV.const_smul (r0^2)).sub (hR.mul hRV)
  have hNear : (fun b : R3 × R3 => fderiv ℝ (nativeEnergyPhase r0 rho r) b V) =ᶠ[𝓝 q]
      (fun b => r0^2*fderiv ℝ rho b V-r b.2*fderiv ℝ r b.2 V.2) := by
    filter_upwards [hRho.eventually (by norm_num)] with b hb
    exact fderiv_nativeEnergyPhase_apply r0 rho r b V
      (hb.differentiableAt (by norm_num)) (hr.differentiable (by simp) b.2)
  have hActualModel := hModel.congr_of_eventuallyEq hNear
  have hdF : DifferentiableAt ℝ (fderiv ℝ (nativeEnergyPhase r0 rho r)) q :=
    ((contDiffAt_nativeEnergyPhase r0 rho r q hRho hr).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hActual := hdF.hasFDerivAt.clm_apply (hasFDerivAt_const V q)
  have hh := congrArg (fun A : (R3 × R3) →L[ℝ] ℝ => A W) (hActual.unique hActualModel)
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul,zero_add,add_zero,
    ev,evR,ContinuousLinearMap.apply_apply,Function.comp_def,map_zero] at hh
  change fderiv ℝ (fderiv ℝ (nativeEnergyPhase r0 rho r)) q W V =
    r0^2*fderiv ℝ (fderiv ℝ rho) q W V-
      (r q.2*fderiv ℝ (fderiv ℝ r) q.2 W.2 V.2+
        fderiv ℝ r q.2 V.2*fderiv ℝ r q.2 W.2) at hh
  nlinarith only [hh]

/-- Exact product covariant Hessian of the SAME phase, with the original profile correction. -/
theorem covariant_second_nativeEnergyPhase_apply
    (r0 : ℝ) (rho : R3 × R3 → ℝ) (r : R3 → ℝ) (q W V : R3 × R3)
    (Gamma1 Gamma2 : R3 →L[ℝ] R3 →L[ℝ] R3)
    (hRho : ContDiffAt ℝ 2 rho q) (hr : ContDiff ℝ ∞ r) :
    fderiv ℝ (fderiv ℝ (nativeEnergyPhase r0 rho r)) q W V-
      fderiv ℝ (nativeEnergyPhase r0 rho r) q (Gamma1 W.1 V.1,Gamma2 W.2 V.2) =
      r0^2*(fderiv ℝ (fderiv ℝ rho) q W V-
        fderiv ℝ rho q (Gamma1 W.1 V.1,Gamma2 W.2 V.2))-
      (fderiv ℝ r q.2 W.2*fderiv ℝ r q.2 V.2+
        r q.2*RadiusProfile.coordinateHessian r (fun A B => Gamma2 A B) q.2 W.2 V.2) := by
  rw [second_fderiv_nativeEnergyPhase_apply r0 rho r q W V hRho hr,
    fderiv_nativeEnergyPhase_apply r0 rho r q _
      (hRho.differentiableAt (by norm_num)) (hr.differentiable (by simp) q.2)]
  simp only [RadiusProfile.coordinateHessian]
  ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
