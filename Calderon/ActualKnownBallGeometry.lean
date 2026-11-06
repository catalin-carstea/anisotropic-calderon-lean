import Calderon.ActualOriginalChartSourceData
import Calderon.FixedExteriorSourceBall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError

theorem exists_known_touching_quarter_ball_of_missing_radiusTwo_point
    (W : Set R3) (hW : IsOpen W) (hWRoom : W ⊆ (radiusTwoOpens : Set R3))
    (hExterior : (exteriorAnnulusOpens : Set R3) ⊆ W)
    (hMissing : ∃ x ∈ (radiusTwoOpens : Set R3), x ∉ W) :
    ∃ center p : R3,
      closedBall center (1/4 : ℝ) ⊆ (radiusTwoOpens : Set R3) ∧
      ball center (1/4 : ℝ) ⊆ W ∧
      p ∈ sphere center (1/4 : ℝ) ∧ p ∈ (radiusTwoOpens : Set R3) ∧
      ‖p‖ ≤ 1 ∧ p ∉ W ∧ p ∈ closure W := by
  have hR2 : ∀ x : R3, x ∈ (radiusTwoOpens : Set R3) ↔ ‖x‖ < 2 := by
    intro x
    change x ∈ ball (0 : R3) 2 ↔ ‖x‖ < 2
    exact mem_ball_zero_iff
  have hAnn : ∀ x : R3, 1 < ‖x‖ → ‖x‖ < 2 → x ∈ W := by
    intro x h1 h2
    have hxA : x ∈ (exteriorAnnulusOpens : Set R3) := by
      change 1 < ‖x‖ ∧ ‖x‖ < 2
      exact ⟨h1, h2⟩
    exact hExterior hxA
  have hKc : IsCompact (closedBall (0 : R3) 1 \ W) := (isCompact_closedBall (0 : R3) 1).diff hW
  obtain ⟨x, hx2, hxW⟩ := hMissing
  have hxK : x ∈ closedBall (0 : R3) 1 \ W := by
    refine ⟨mem_closedBall_zero_iff.mpr ?_, hxW⟩
    by_contra hx1
    exact hxW (hAnn x (not_le.mp hx1) ((hR2 x).mp hx2))
  obtain ⟨p, hpK, hpMax⟩ := hKc.exists_isMaxOn ⟨x, hxK⟩ continuous_norm.continuousOn
  have hMax : ∀ y ∈ closedBall (0 : R3) 1 \ W, ‖y‖ ≤ ‖p‖ := isMaxOn_iff.mp hpMax
  have hp1 : ‖p‖ ≤ 1 := mem_closedBall_zero_iff.mp hpK.1
  obtain ⟨v, hv1, hpv⟩ : ∃ v : R3, ‖v‖ = 1 ∧ p = ‖p‖ • v := by
    by_cases hp0 : p = 0
    · refine ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), ?_, ?_⟩
      · rw [EuclideanSpace.norm_single, norm_one]
      · rw [hp0, norm_zero, zero_smul]
    · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
      refine ⟨‖p‖⁻¹ • p, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  obtain ⟨c, hcn, hpc⟩ : ∃ c : R3, ‖c‖ = ‖p‖ + 1/4 ∧ ‖p - c‖ = 1/4 := by
    refine ⟨p + (1/4 : ℝ) • v, ?_, ?_⟩
    · have hc : p + (1/4 : ℝ) • v = (‖p‖ + 1/4) • v := by
        rw [add_smul, ← hpv]
      have hnn : (0 : ℝ) ≤ ‖p‖ + 1/4 := by positivity
      rw [hc, norm_smul, hv1, mul_one, Real.norm_of_nonneg hnn]
    · have hd : p - (p + (1/4 : ℝ) • v) = -((1/4 : ℝ) • v) :=
        sub_add_cancel_left p ((1/4 : ℝ) • v)
      have hq : (0 : ℝ) ≤ 1/4 := by norm_num
      rw [hd, norm_neg, norm_smul, hv1, mul_one, Real.norm_of_nonneg hq]
  have hClosed : closedBall c (1/4 : ℝ) ⊆ (radiusTwoOpens : Set R3) := by
    intro y hy
    have hyc : ‖y - c‖ ≤ 1/4 := mem_closedBall_iff_norm.mp hy
    have hUp := norm_le_norm_sub_add y c
    exact (hR2 y).mpr (by linarith)
  have hOpen : ball c (1/4 : ℝ) ⊆ W := by
    intro y hy
    have hyc : ‖y - c‖ < 1/4 := mem_ball_iff_norm.mp hy
    have hUp := norm_le_norm_sub_add y c
    have hLow := norm_le_norm_sub_add c y
    rw [norm_sub_rev c y] at hLow
    have hy2 : ‖y‖ < 2 := by linarith
    have hyp : ‖p‖ < ‖y‖ := by linarith
    by_contra hyW
    by_cases hy1 : ‖y‖ ≤ 1
    · have hyK : y ∈ closedBall (0 : R3) 1 \ W := ⟨mem_closedBall_zero_iff.mpr hy1, hyW⟩
      exact absurd (hMax y hyK) (not_le.mpr hyp)
    · exact hyW (hAnn y (not_le.mp hy1) hy2)
  have hpS : p ∈ sphere c (1/4 : ℝ) := mem_sphere_iff_norm.mpr hpc
  refine ⟨c, p, hClosed, hOpen, hpS, (hR2 p).mpr (by linarith), hp1, hpK.2, ?_⟩
  refine closure_mono hOpen ?_
  rw [closure_ball c (by norm_num : (1/4 : ℝ) ≠ 0)]
  exact sphere_subset_closedBall hpS

theorem exists_regular_one_sided_separator_of_known_physical_ball
    (U W : Set R3) (hU : IsOpen U) (h0 : (0 : R3) ∈ U)
    (Xi : R3 → R3) (hXi : ContDiffOn ℝ ∞ Xi U)
    (hJac : IsUnit (coordinateJacobianMatrix Xi 0).det)
    (center : R3) (r : ℝ) (hr : 0 < r) (hTouch : Xi 0 ∈ sphere center r)
    (hBall : ball center r ⊆ W) :
    ∃ sep : R3 → ℝ,
      sep = (fun z => ‖Xi z-center‖^2-r^2) ∧
      ContDiffOn ℝ ∞ sep U ∧ sep 0 = 0 ∧ fderiv ℝ sep 0 ≠ 0 ∧
      ∃ a : ℝ, 0 < a ∧ ball (0 : R3) a ⊆ U ∧
        {z ∈ ball (0 : R3) a | sep z < 0} ⊆ Xi ⁻¹' W := by
  have hN : ‖Xi 0 - center‖ = r := mem_sphere_iff_norm.mp hTouch
  have hXiAt : ContDiffAt ℝ ∞ Xi 0 := hXi.contDiffAt (hU.mem_nhds h0)
  have hDiff : DifferentiableAt ℝ Xi 0 := hXiAt.differentiableAt (by simp)
  have hSep : HasFDerivAt (fun z => ‖Xi z - center‖ ^ 2 - r ^ 2)
      (2 • (innerSL ℝ (Xi 0 - center)).comp (fderiv ℝ Xi 0)) 0 :=
    (hDiff.hasFDerivAt.sub_const center).norm_sq.sub_const (r ^ 2)
  have hInj : Function.Injective (fderiv ℝ Xi 0) :=
    injective_fderiv_of_unit_coordinate_jacobian Xi 0 hJac
  have hSurj : Function.Surjective (fderiv ℝ Xi 0) :=
    (LinearMap.injective_iff_surjective (f := (fderiv ℝ Xi 0 : R3 →ₗ[ℝ] R3))).mp hInj
  obtain ⟨w, hw⟩ := hSurj (Xi 0 - center)
  refine ⟨fun z => ‖Xi z - center‖ ^ 2 - r ^ 2, rfl, ?_, ?_, ?_, ?_⟩
  · exact ((hXi.sub contDiffOn_const).norm_sq ℝ).sub contDiffOn_const
  · show ‖Xi 0 - center‖ ^ 2 - r ^ 2 = 0
    rw [hN, sub_self]
  · intro hZero
    have hVal : fderiv ℝ (fun z => ‖Xi z - center‖ ^ 2 - r ^ 2) 0 w = 2 * r ^ 2 := by
      rw [hSep.fderiv]
      rw [two_smul, ContinuousLinearMap.add_apply]
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, hw,
        real_inner_self_eq_norm_sq, hN]
      ring
    rw [hZero, ContinuousLinearMap.zero_apply] at hVal
    have hPos : (0 : ℝ) < 2 * r ^ 2 := mul_pos two_pos (pow_pos hr 2)
    linarith
  · obtain ⟨a, ha, haU⟩ := Metric.isOpen_iff.mp hU 0 h0
    refine ⟨a, ha, haU, ?_⟩
    rintro z ⟨-, hz⟩
    have hz' : ‖Xi z - center‖ ^ 2 - r ^ 2 < 0 := hz
    have hLt : ‖Xi z - center‖ < r := by
      by_contra hGe
      have hGe' : r ≤ ‖Xi z - center‖ := not_lt.mp hGe
      nlinarith [mul_nonneg (sub_nonneg.mpr hGe') (add_nonneg (norm_nonneg (Xi z - center)) hr.le)]
    exact hBall (mem_ball_iff_norm.mpr hLt)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
