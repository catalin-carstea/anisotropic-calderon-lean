import Calderon.ConformalFluxDivergence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator

def inverseNormPotential (c0 : ℝ) (z : R3) : ℝ := c0 / ‖z‖

private theorem hasFDerivAt_R3_norm_off_zero (z : R3) (hz : z ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun w : R3 => ‖w‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have heq : (fun w : R3 => Real.sqrt (‖w‖^2)) = (fun w : R3 => ‖w‖) := by
    funext w
    exact Real.sqrt_sq (norm_nonneg w)
  rw [heq] at h
  apply h.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
    Real.sqrt_sq (norm_nonneg z), nsmul_eq_mul]
  field_simp
  norm_num

theorem contDiffOn_inverseNormPotential (c0 : ℝ) :
    ContDiffOn ℝ ∞ (inverseNormPotential c0) ({0}ᶜ : Set R3) := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact (contDiffAt_const.div (contDiffAt_norm ℝ hz0) (norm_ne_zero_iff.mpr hz0)).contDiffWithinAt

theorem hasFDerivAt_inverseNormPotential (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (inverseNormPotential c0) (-(c0 / ‖z‖^3) • innerSL ℝ z) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hScalar := (hasDerivAt_const ‖z‖ c0).fun_div (hasDerivAt_id ‖z‖) hn
  have h := hScalar.comp_hasFDerivAt z (hasFDerivAt_R3_norm_off_zero z hz)
  change HasFDerivAt (𝕜 := ℝ) (inverseNormPotential c0) _ z at h
  apply h.congr_fderiv
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, id_eq, Pi.pow_apply]
  field_simp
  <;> ring

theorem gradient_inverseNormPotential (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    gradient (inverseNormPotential c0) z = -(c0 / ‖z‖^3) • z := by
  apply ext_inner_right ℝ
  intro h
  rw [inner_gradient_left, (hasFDerivAt_inverseNormPotential c0 z hz).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, real_inner_smul_left]

theorem energyGradient_inverseNormPotential (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    energyGradient (inverseNormPotential c0) z = -(c0 / ‖z‖^3) • z := by
  rw [energyGradient_eq_gradient, gradient_inverseNormPotential c0 z hz]

theorem hasFDerivAt_gradient_inverseNormPotential (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (gradient (inverseNormPotential c0))
      ((3*c0 / ‖z‖^5) • (innerSL ℝ z).smulRight z -
        (c0 / ‖z‖^3) • ContinuousLinearMap.id ℝ R3) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hScalar := (hasDerivAt_const ‖z‖ (-c0)).fun_div
    ((hasDerivAt_id ‖z‖).pow 3) (pow_ne_zero 3 hn)
  have hCoeff : HasFDerivAt (𝕜 := ℝ) (fun w : R3 => -(c0 / ‖w‖^3))
      ((3*c0 / ‖z‖^5) • innerSL ℝ z) z := by
    have h := hScalar.comp_hasFDerivAt z (hasFDerivAt_R3_norm_off_zero z hz)
    simp only [neg_div] at h
    apply h.congr_fderiv
    ext v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, id_eq, Pi.pow_apply]
    field_simp
    <;> ring
  have hField : HasFDerivAt (𝕜 := ℝ) (fun w : R3 => -(c0 / ‖w‖^3) • w)
      ((3*c0 / ‖z‖^5) • (innerSL ℝ z).smulRight z -
        (c0 / ‖z‖^3) • ContinuousLinearMap.id ℝ R3) z := by
    have h := hCoeff.smul (hasFDerivAt_id z)
    simp only [Pi.smul_apply, id_eq] at h
    apply h.congr_fderiv
    ext v i
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, PiLp.smul_apply,
      PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have hGerm : gradient (inverseNormPotential c0) =ᶠ[𝓝 z]
      (fun w : R3 => -(c0 / ‖w‖^3) • w) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({0}ᶜ : Set R3) by simpa using hz)] with w hw
    exact gradient_inverseNormPotential c0 w (by simpa using hw)
  exact hField.congr_of_eventuallyEq hGerm

theorem fderiv_gradient_inverseNormPotential_apply
    (c0 : ℝ) (z : R3) (hz : z ≠ 0) (h : R3) :
    fderiv ℝ (gradient (inverseNormPotential c0)) z h =
      (3*c0 / ‖z‖^5 * inner ℝ z h) • z - (c0 / ‖z‖^3) • h := by
  rw [(hasFDerivAt_gradient_inverseNormPotential c0 z hz).fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    smul_smul]

theorem coordinateFluxDivergence_gradient_inverseNormPotential
    (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    coordinateFluxDivergence (gradient (inverseNormPotential c0)) z = 0 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hHess := hasFDerivAt_gradient_inverseNormPotential c0 z hz
  have hTerm (i : Fin 3) :
      fderiv ℝ (fun w => gradient (inverseNormPotential c0) w i) z
          (NormalCoordinatesFrame.coordinateVector i) =
        3*c0 / ‖z‖^5 * (z i)^2 - c0 / ‖z‖^3 := by
    have hp := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hHess
    have hEval : (fun w : R3 => gradient (inverseNormPotential c0) w i) =
        (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ gradient (inverseNormPotential c0) := rfl
    rw [hEval, hp.fderiv]
    simp [ContinuousLinearMap.comp_apply, NormalCoordinatesFrame.coordinateVector,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right, Pi.single_apply, pow_two]
    <;> ring
  unfold coordinateFluxDivergence
  simp_rw [hTerm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

theorem norm_gradient_inverseNormPotential
    (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    ‖gradient (inverseNormPotential c0) z‖ = |c0| / ‖z‖^2 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [gradient_inverseNormPotential c0 z hz, norm_smul, Real.norm_eq_abs]
  simp only [abs_neg, abs_div, abs_pow, abs_of_nonneg (norm_nonneg z)]
  field_simp
  <;> ring

theorem norm_fderiv_gradient_inverseNormPotential_le
    (c0 : ℝ) (z : R3) (hz : z ≠ 0) :
    ‖fderiv ℝ (gradient (inverseNormPotential c0)) z‖ ≤ 4*|c0| / ‖z‖^3 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [fderiv_gradient_inverseNormPotential_apply c0 z hz h]
  calc
    _ ≤ ‖(3*c0 / ‖z‖^5 * inner ℝ z h) • z‖ + ‖(c0 / ‖z‖^3) • h‖ := norm_sub_le _ _
    _ = (3*|c0| / ‖z‖^5 * |inner ℝ z h|) * ‖z‖ + (|c0| / ‖z‖^3) * ‖h‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
        abs_of_nonneg (norm_nonneg z), abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ ≤ (3*|c0| / ‖z‖^5 * (‖z‖*‖h‖)) * ‖z‖ + (|c0| / ‖z‖^3) * ‖h‖ := by
      gcongr
      exact abs_real_inner_le_norm z h
    _ = (4*|c0| / ‖z‖^3) * ‖h‖ := by
      field_simp
      <;> ring

end OAI.AnisotropicCalderon.ConnectionError
