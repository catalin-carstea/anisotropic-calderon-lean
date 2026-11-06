import Calderon.LocalSmoothAmbientExtension

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem gradient_comp_const_smul
    (f : R3 → ℝ) (a : ℝ) (x : R3) (hf : DifferentiableAt ℝ f (a • x)) :
    gradient (fun y : R3 => f (a • y)) x = a • gradient f (a • x) := by
  let A : R3 →L[ℝ] R3 := a • ContinuousLinearMap.id ℝ R3
  have hA (y : R3) : A y = a • y := rfl
  have hComp : HasFDerivAt (fun y : R3 => f (a • y))
      ((fderiv ℝ f (a • x)).comp A) x :=
    hf.hasFDerivAt.comp x A.hasFDerivAt
  apply (innerSL_inj (𝕜 := ℝ)).mp
  ext v
  change inner ℝ (gradient (fun y : R3 => f (a • y)) x) v =
    inner ℝ (a • gradient f (a • x)) v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left,hComp.fderiv]
  simp only [ContinuousLinearMap.comp_apply,hA,map_smul,smul_eq_mul]

theorem exists_smoothData_inward_dilation_eq_near_closedBall
    (f : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f (ballOpens : Set R3))
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ w : SmoothData, HasCompactSupport w.1 ∧
      ∀ x ∈ closedBall (0 : R3) 1,
        (w.1 =ᶠ[𝓝 x] (fun y : R3 => f (a • y))) ∧
        w.1 x = f (a • x) ∧ gradient w.1 x = a • gradient f (a • x) := by
  let S : Set R3 := (fun x : R3 => a • x) ⁻¹' (ballOpens : Set R3)
  have hLin : Continuous (fun x : R3 => a • x) :=
    (continuous_const : Continuous (fun _ : R3 => a)).smul continuous_id
  have hS : IsOpen S := ballOpens.isOpen.preimage hLin
  have hKS : closedBall (0 : R3) 1 ⊆ S := by
    intro x hx
    have hxNorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
    change a • x ∈ ball (0 : R3) 1
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
    calc
      a * ‖x‖ ≤ a * 1 := mul_le_mul_of_nonneg_left hxNorm ha0.le
      _ < 1 := by simpa only [mul_one] using ha1
  have hScalar : ContDiff ℝ ∞ (fun _ : R3 => a) := contDiff_const
  have hVector : ContDiff ℝ ∞ (fun x : R3 => x) := contDiff_id
  have hDilation : ContDiff ℝ ∞ (fun x : R3 => a • x) := hScalar.smul hVector
  have hSmooth : ContDiffOn ℝ ∞ (fun x : R3 => f (a • x)) S :=
    hf.comp hDilation.contDiffOn (fun _ hx => hx)
  obtain ⟨w,hwc,hw⟩ := exists_smoothData_eq_near_compact
    (closedBall (0 : R3) 1) S (isCompact_closedBall _ _) hS hKS
    (fun x : R3 => f (a • x)) hSmooth
  refine ⟨w,hwc,fun x hx => ⟨hw x hx,(hw x hx).eq_of_nhds,?_⟩⟩
  rw [(hw x hx).gradient_eq]
  exact gradient_comp_const_smul f a x
    ((hf.contDiffAt (ballOpens.isOpen.mem_nhds (hKS hx))).differentiableAt (by simp))

end OAI.AnisotropicCalderon.DirichletFamily
