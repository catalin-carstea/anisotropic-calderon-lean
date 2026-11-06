import Calderon.NativePolynomialBallSobolev
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily

theorem tendsto_integral_norm_sq_dilation_sub_of_continuous_compactSupport
    {V : Type*} [NormedAddCommGroup V]
    (g : R3 → V) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun a : ℝ => ∫ x : R3, ‖g (a • x) - g x‖^2) (𝓝 1) (𝓝 0) := by
  have hRadius : ∃ R : ℝ, 0 < R ∧ ∀ x ∈ tsupport g, ‖x‖ < R :=
    hgc.isBounded.exists_pos_norm_lt
  obtain ⟨R,hR,hSupport⟩ := hRadius
  have hUniform : ∃ M0 : ℝ, ∀ x : R3, ‖g x‖ ≤ M0 :=
    hgc.exists_bound_of_continuous hg
  obtain ⟨M0,hM0⟩ := hUniform
  let M : ℝ := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hgBound (x : R3) : ‖g x‖ ≤ M := (hM0 x).trans (le_max_left _ _)
  have hZero (x : R3) (hx : R ≤ ‖x‖) : g x = 0 := by
    by_contra hn
    have hs : ‖x‖ < R := hSupport x (subset_tsupport g hn)
    exact (not_lt_of_ge hx hs)
  let bound : R3 → ℝ := (closedBall (0 : R3) (2*R)).indicator (fun _ => 4*M^2)
  have hbInt : Integrable bound (volume : Measure R3) := by
    change Integrable ((closedBall (0 : R3) (2*R)).indicator
      (fun _ : R3 => (4*M^2 : ℝ))) (volume : Measure R3)
    apply (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
    exact integrableOn_const (isCompact_closedBall (0 : R3) (2*R)).measure_lt_top.ne
  have hMeas : ∀ᶠ a : ℝ in 𝓝 1,
      AEStronglyMeasurable (fun x : R3 => ‖g (a • x) - g x‖^2) (volume : Measure R3) :=
    Eventually.of_forall fun a =>
      (show Continuous (fun x : R3 => ‖g (a • x) - g x‖^2) from
        ((hg.comp ((continuous_const : Continuous (fun _ : R3 => a)).smul
          continuous_id)).sub hg).norm.pow 2).aestronglyMeasurable
  have hBound : ∀ᶠ a : ℝ in 𝓝 1, ∀ᵐ x : R3 ∂(volume : Measure R3),
      ‖‖g (a • x) - g x‖^2‖ ≤ bound x := by
    filter_upwards [Ioi_mem_nhds (show (1/2 : ℝ) < 1 by norm_num)] with a ha
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    by_cases hx : x ∈ closedBall (0 : R3) (2*R)
    · rw [show bound x = 4*M^2 from Set.indicator_of_mem hx _]
      have hd : ‖g (a • x) - g x‖ ≤ 2*M :=
        (norm_sub_le _ _).trans (by linarith only [hgBound (a • x),hgBound x])
      nlinarith only [hd,hM,norm_nonneg (g (a • x) - g x)]
    · have hxR : 2*R < ‖x‖ := by
        simpa only [mem_closedBall,dist_zero_right,not_le] using hx
      have hax : R ≤ ‖a • x‖ := by
        have ha0 : 0 < a := lt_trans (by norm_num : (0 : ℝ) < 1/2) ha
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
        have ha' : (1/2 : ℝ) < a := ha
        calc
          R ≤ (1/2 : ℝ) * ‖x‖ := by linarith only [hxR]
          _ ≤ a * ‖x‖ := mul_le_mul_of_nonneg_right ha'.le (norm_nonneg x)
      rw [hZero (a • x) hax,hZero x (by linarith only [hxR,hR]),sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
      rw [show bound x = 0 from Set.indicator_of_notMem hx _]
  have hLim : ∀ᵐ x : R3 ∂(volume : Measure R3),
      Tendsto (fun a : ℝ => ‖g (a • x) - g x‖^2) (𝓝 1) (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    have hax : Tendsto (fun a : ℝ => a • x) (𝓝 1) (𝓝 x) := by
      simpa only [id_eq,one_smul] using (tendsto_id.smul tendsto_const_nhds :
        Tendsto (fun a : ℝ => a • x) (𝓝 1) (𝓝 ((1 : ℝ) • x)))
    have hgax : Tendsto (fun a : ℝ => g (a • x)) (𝓝 1) (𝓝 (g x)) :=
      (hg.tendsto x).comp hax
    have hsub : Tendsto (fun a : ℝ => g (a • x) - g x) (𝓝 1) (𝓝 (g x - g x)) :=
      hgax.sub tendsto_const_nhds
    simpa only [sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using hsub.norm.pow 2
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure R3)) (l := 𝓝 (1 : ℝ))
      (F := fun (a : ℝ) (x : R3) => ‖g (a • x) - g x‖^2)
      (f := fun _ : R3 => (0 : ℝ)) bound hMeas hBound hbInt hLim

end OAI.AnisotropicCalderon.DirichletFamily
