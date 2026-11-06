import Calderon.MetricPullbackFlux
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.NativeSourceChartCalculus
open ConnectionError MetricOperator MetricVolume

lemma pullbackMetric_eq_original_D (g : MatrixField) (X : R3 → R3) (x : R3) :
    pullbackMetric g X x = (D X x).transpose * g (X x) * D X x := by
  have hD (y : R3) : D X y = coordinateJacobianMatrix X y := rfl
  calc
    pullbackMetric g X x = (coordinateJacobianMatrix X x).transpose *
        g (X x) * coordinateJacobianMatrix X x := by
      simp only [pullbackMetric, operatorMatrixMap_comp, operatorMatrixMap_adjoint,
        operatorMatrixMap_metricOperatorField, coordinateJacobianMatrix_eq_operatorMatrixMap,
        Matrix.mul_assoc]
    _ = _ := by rw [← hD x]

lemma comp_eq_id_of_same_chart_hasFDerivAt
    (Φ : R3 → R3) (e : OpenPartialHomeomorph R3 R3) (y : R3) (hy : y ∈ e.target)
    (hForward : (e : R3 → R3) = Φ) (A B : R3 →L[ℝ] R3)
    (hΦ : HasFDerivAt Φ A (e.symm y)) (hInv : HasFDerivAt (e.symm : R3 → R3) B y) :
    A.comp B = ContinuousLinearMap.id ℝ R3 := by
  have hNearTarget : ∀ᶠ z in 𝓝 y, z ∈ e.target := IsOpen.mem_nhds e.open_target hy
  have hNear : (fun z : R3 => z) =ᶠ[𝓝 y] (fun z => Φ (e.symm z)) := by
    filter_upwards [hNearTarget] with z hz
    rw [← hForward]
    exact (e.right_inv hz).symm
  have hComp : HasFDerivAt (fun z : R3 => Φ (e.symm z)) (A.comp B) y := by
    simpa only [Function.comp_def] using hΦ.comp y hInv
  have hId : HasFDerivAt (fun z : R3 => z) (A.comp B) y :=
    hComp.congr_of_eventuallyEq hNear
  exact hId.unique (hasFDerivAt_id y)

lemma inverse_bounds_of_norm_sub_id_le_half
    (A B : R3 →L[ℝ] R3)
    (hApprox : ‖A - ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ))
    (hInv : A.comp B = ContinuousLinearMap.id ℝ R3) :
    ∀ v : R3, (2/3 : ℝ) * ‖v‖ ≤ ‖B v‖ ∧ ‖B v‖ ≤ 2 * ‖v‖ := by
  have hNormA : ‖A‖ ≤ (3/2 : ℝ) := by
    have h := norm_add_le (A-ContinuousLinearMap.id ℝ R3) (ContinuousLinearMap.id ℝ R3)
    rw [sub_add_cancel] at h
    have hId := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := R3)
    linarith
  have hLowerA (w : R3) : (1/2 : ℝ) * ‖w‖ ≤ ‖A w‖ := by
    have hErr : ‖(A-ContinuousLinearMap.id ℝ R3) w‖ ≤ (1/2 : ℝ) * ‖w‖ :=
      ((A-ContinuousLinearMap.id ℝ R3).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right hApprox (norm_nonneg w))
    have hDiff : A w - (A-ContinuousLinearMap.id ℝ R3) w = w := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      abel
    have h := norm_sub_le (A w) ((A-ContinuousLinearMap.id ℝ R3) w)
    rw [hDiff] at h
    linarith
  intro v
  have hAB : A (B v) = v := by
    have h := congrArg (fun T : R3 →L[ℝ] R3 => T v) hInv
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  have hUpper : ‖v‖ ≤ (3/2 : ℝ) * ‖B v‖ := by
    calc
      ‖v‖ = ‖A (B v)‖ := congrArg norm hAB.symm
      _ ≤ ‖A‖ * ‖B v‖ := A.le_opNorm (B v)
      _ ≤ (3/2 : ℝ) * ‖B v‖ := mul_le_mul_of_nonneg_right hNormA (norm_nonneg _)
  have hLower := hLowerA (B v)
  rw [hAB] at hLower
  constructor <;> linarith

end OAI.AnisotropicCalderon.NativeSourceChartCalculus
