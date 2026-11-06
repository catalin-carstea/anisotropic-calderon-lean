import Calderon.InverseNormPotentialCalderon
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError

def regularizedInverseNormPotential (c0 t : ℝ) (z : R3) : ℝ :=
  c0 * (‖z‖^2+t)^(-1/2 : ℝ)

theorem regularizedInverseNormPotential_zero (c0 : ℝ) (z : R3) :
    regularizedInverseNormPotential c0 0 z = inverseNormPotential c0 z := by
  unfold regularizedInverseNormPotential inverseNormPotential
  rw [add_zero,show (-1/2 : ℝ) = -(1/2 : ℝ) by ring,
    Real.rpow_neg (sq_nonneg ‖z‖),← Real.sqrt_eq_rpow,Real.sqrt_sq (norm_nonneg z)]
  rfl

theorem contDiff_regularizedInverseNormPotential (c0 t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ∞ (regularizedInverseNormPotential c0 t) := by
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne
    (fun z => (add_pos_of_nonneg_of_pos (sq_nonneg ‖z‖) ht).ne'))

theorem hasFDerivAt_regularizedInverseNormPotential
    (c0 t : ℝ) (ht : 0 < t) (z : R3) :
    HasFDerivAt (𝕜 := ℝ) (regularizedInverseNormPotential c0 t)
      (-(c0 * (‖z‖^2+t)^(-3/2 : ℝ)) • innerSL ℝ z) z := by
  have hpos : 0 < ‖z‖^2+t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const t).rpow_const
    (p := (-1/2 : ℝ)) (Or.inl hpos.ne')).const_mul c0
  apply h.congr_fderiv
  ext v
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,nsmul_eq_mul]
  norm_num
  ring

theorem gradient_regularizedInverseNormPotential
    (c0 t : ℝ) (ht : 0 < t) (z : R3) :
    gradient (regularizedInverseNormPotential c0 t) z =
      -(c0 * (‖z‖^2+t)^(-3/2 : ℝ)) • z := by
  apply ext_inner_right ℝ
  intro h
  rw [inner_gradient_left,(hasFDerivAt_regularizedInverseNormPotential c0 t ht z).fderiv]
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,real_inner_smul_left]

theorem hasFDerivAt_gradient_regularizedInverseNormPotential
    (c0 t : ℝ) (ht : 0 < t) (z : R3) :
    HasFDerivAt (𝕜 := ℝ) (gradient (regularizedInverseNormPotential c0 t))
      ((3*c0 * (‖z‖^2+t)^(-5/2 : ℝ)) • (innerSL ℝ z).smulRight z -
        (c0 * (‖z‖^2+t)^(-3/2 : ℝ)) • ContinuousLinearMap.id ℝ R3) z := by
  have hpos : 0 < ‖z‖^2+t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have hCoeff : HasFDerivAt (𝕜 := ℝ)
      (fun w : R3 => -(c0 * (‖w‖^2+t)^(-3/2 : ℝ)))
      ((3*c0 * (‖z‖^2+t)^(-5/2 : ℝ)) • innerSL ℝ z) z := by
    have h := ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const t).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hpos.ne')).const_mul c0).neg
    apply h.congr_fderiv
    ext v
    simp only [neg_apply,smul_apply,
      innerSL_apply_apply,smul_eq_mul,nsmul_eq_mul]
    norm_num
    ring
  have hField := hCoeff.smul (hasFDerivAt_id z)
  have hActual : HasFDerivAt (𝕜 := ℝ)
      (fun w : R3 => -(c0 * (‖w‖^2+t)^(-3/2 : ℝ)) • w)
      ((3*c0 * (‖z‖^2+t)^(-5/2 : ℝ)) • (innerSL ℝ z).smulRight z -
        (c0 * (‖z‖^2+t)^(-3/2 : ℝ)) • ContinuousLinearMap.id ℝ R3) z := by
    apply hField.congr_fderiv
    ext v i
    simp only [add_apply,sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply,innerSL_apply_apply,PiLp.smul_apply,
      PiLp.add_apply,PiLp.sub_apply,smul_eq_mul,id_eq]
    ring
  have hEq : gradient (regularizedInverseNormPotential c0 t) =
      (fun w : R3 => -(c0 * (‖w‖^2+t)^(-3/2 : ℝ)) • w) :=
    funext (gradient_regularizedInverseNormPotential c0 t ht)
  rw [hEq]
  exact hActual

theorem fderiv_gradient_regularizedInverseNormPotential_apply
    (c0 t : ℝ) (ht : 0 < t) (z h : R3) :
    fderiv ℝ (gradient (regularizedInverseNormPotential c0 t)) z h =
      (3*c0 * (‖z‖^2+t)^(-5/2 : ℝ) * inner ℝ z h) • z -
        (c0 * (‖z‖^2+t)^(-3/2 : ℝ)) • h := by
  rw [(hasFDerivAt_gradient_regularizedInverseNormPotential c0 t ht z).fderiv]
  simp only [sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply,smul_smul]

end OAI.AnisotropicCalderon.ConnectionError
