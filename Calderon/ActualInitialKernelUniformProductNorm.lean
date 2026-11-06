import Calderon.ActualInitialKernelUniformBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise NNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable

theorem exists_uniform_initialKernel_product_L2_bound
    (S : KnownSideSourceData) (B d : ℝ) (hB : 0 < B) (hd : 0 < d) :
    ∃ (lambda0 N : ℝ), 0 < lambda0 ∧ lambda0 ≤ 1 ∧ 0 < N ∧
      ∀ lambda ∈ Ioc (0:ℝ) lambda0, ∀ A V : Set R3,
      MeasurableSet A → MeasurableSet V → A ×ˢ V ⊆ fixedSeparationSet B d →
      ∀ F : R3 × R3 → ℝ, EqOn F (initialKernel S lambda) (A ×ˢ V) →
      ∀ hF : MemLp F 2 (((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)),
        ‖hF.toLp F‖ ≤ N := by
  obtain ⟨lambda0,M,hl,hl1,hM,hBound⟩ := exists_uniform_initialKernel_fixed_separation_bound S B d hB hd
  let m : Measure R3 := (volume:Measure R3).restrict (closedBall (0:R3) B)
  let nu0 : Measure (R3 × R3) := m.prod m
  letI : IsFiniteMeasure m := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall (0:R3) B).measure_lt_top.ne
  letI : IsFiniteMeasure nu0 := by dsimp only [nu0];infer_instance
  let Z : ℝ≥0∞ := nu0 univ ^ ((2:ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal M
  have hZ : Z ≠ (⊤:ℝ≥0∞) := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top nu0 univ)) ENNReal.ofReal_ne_top
  refine ⟨lambda0,Z.toReal+1,hl,hl1,by positivity,?_⟩
  intro lambda hlambda A V hA hV hSub F hEq hF
  have hAeMem : ∀ᵐ z ∂(((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)),
      z ∈ A ×ˢ V := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hA.prod hV)
  have hAeBound : ∀ᵐ z ∂(((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)), ‖F z‖ ≤ M := by
    filter_upwards [hAeMem] with z hz
    rw [hEq hz,Real.norm_eq_abs]
    exact hBound lambda hlambda z (hSub hz)
  have hAV : ((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V) ≤ nu0 := by
    by_cases hAVempty : (A ×ˢ V).Nonempty
    · obtain ⟨z,hz⟩ := hAVempty
      have hAroom : A ⊆ closedBall (0:R3) B := by
        intro x hx
        exact mem_closedBall_zero_iff.mpr (@hSub (x,z.2) ⟨hx,hz.2⟩).1
      have hVroom : V ⊆ closedBall (0:R3) B := by
        intro y hy
        exact mem_closedBall_zero_iff.mpr (@hSub (z.1,y) ⟨hz.1,hy⟩).2.1
      exact Measure.prod_mono (Measure.restrict_mono_set _ hAroom) (Measure.restrict_mono_set _ hVroom)
    · have hEmpty : A ×ˢ V = ∅ := Set.not_nonempty_iff_eq_empty.mp hAVempty
      rw [Measure.prod_restrict,hEmpty,Measure.restrict_empty]
      exact bot_le
  have hElp : eLpNorm F 2 (((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)) ≤ Z := by
    have h := eLpNorm_le_of_ae_bound (p:=2) hF.aestronglyMeasurable hAeBound
    refine h.trans ?_
    dsimp only [Z]
    gcongr
  rw [Lp.norm_toLp]
  exact (ENNReal.toReal_mono hZ hElp).trans (by linarith)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
