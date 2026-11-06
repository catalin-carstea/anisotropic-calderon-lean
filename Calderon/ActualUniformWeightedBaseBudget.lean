import Calderon.WeightedBaseSpectral
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.WeightedBaseSpectral
open SphereHarmonic ReferenceDensityBounds

theorem exists_uniform_referenceBaseLift_bound_of_supported_pointwise_bound
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L B:ℝ):
    ∃ C:ℝ,0 < C ∧ ∀ q∈Icc (0:ℝ) 1,∀ (V:R3→SphereL2) (hV:Continuous V) (hVc:HasCompactSupport V),
      tsupport V⊆closedBall (0:R3) B → ∀ M:ℝ,0 ≤ M →
      (∀ y∈closedBall (0:R3) B,‖V y‖ ≤ M) → ‖referenceBaseLift g hg L q V hV hVc‖ ≤ C*M := by
  let K:Set R3 := closedBall (0:R3) B
  have hK:IsCompact K := isCompact_closedBall _ _
  obtain ⟨A0,hA0⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (contDiff_referenceDensityFamily g hg L).continuous.continuousOn
  let A:ℝ := max A0 1
  have hA:0 < A := zero_lt_one.trans_le (le_max_right _ _)
  let T:ℝ := A*volume.real K
  have hT:0 ≤ T := mul_nonneg hA.le ENNReal.toReal_nonneg
  let C:ℝ := T+1
  have hC:0 < C := by dsimp only [C];linarith only [hT]
  have hCT:T ≤ C^2 := by dsimp only [C];nlinarith only [hT,sq_nonneg T]
  refine ⟨C,hC,?_⟩
  intro q hq V hV hVc hSupp M hM hBound
  letI:IsFiniteMeasure ((volume:Measure R3).restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let f:R3→ℝ := fun y => referenceDensityFamily g L (q,y)*‖V y‖^2
  have hAe:∀ᵐ y∂((volume:Measure R3).restrict K),‖f y‖ ≤ A*M^2 := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    have hDensity:‖referenceDensityFamily g L (q,y)‖ ≤ A :=
      (hA0 (q,y) ⟨hq,hy⟩).trans (le_max_left _ _)
    dsimp only [f]
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul hDensity (pow_le_pow_left₀ (norm_nonneg _) (hBound y hy) 2)
      (sq_nonneg _) hA.le
  have hIntegral:‖∫ y,f y‖ ≤ T*M^2 := by
    have hEq:(∫ y in K,f y)=(∫ y,f y) := setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      have hz:V y=0 := image_eq_zero_of_notMem_tsupport (fun hh => hy (hSupp hh))
      simp only [f,hz,norm_zero,zero_pow (by norm_num:2≠0),mul_zero]
    rw [← hEq]
    have h:=norm_integral_le_of_norm_le_const hAe
    have hm:((volume:Measure R3).restrict K).real univ=volume.real K := by simp [Measure.real]
    rw [hm] at h
    exact h.trans_eq (by dsimp only [T];ring)
  have hsq:‖referenceBaseLift g hg L q V hV hVc‖^2 ≤ (C*M)^2 := by
    calc
      _ = ∫ y,f y := norm_sq_referenceBaseLift g hg L q V hV hVc
      _ ≤ ‖∫ y,f y‖ := le_abs_self _
      _ ≤ T*M^2 := hIntegral
      _ ≤ C^2*M^2 := mul_le_mul_of_nonneg_right hCT (sq_nonneg M)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.le hM)).mp hsq

end OAI.AnisotropicCalderon.WeightedBaseSpectral
