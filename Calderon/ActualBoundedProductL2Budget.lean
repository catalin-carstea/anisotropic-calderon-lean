import MixedKernelCurrentCrossBounds
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_bounded_product_L2_norm_budget (B:ℝ) :
    ∃ C:ℝ,0 < C ∧ ∀ A V:Set R3,MeasurableSet A → MeasurableSet V →
      A⊆closedBall (0:R3) B → V⊆closedBall (0:R3) B → ∀ F:R3×R3→ℝ,
      ∀ hF:MemLp F 2 (((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)),
      ∀ M:ℝ,0 ≤ M → (∀ z∈A×ˢV,‖F z‖ ≤ M) → ‖hF.toLp F‖ ≤ C*M := by
  let m:Measure R3 := (volume:Measure R3).restrict (closedBall (0:R3) B)
  let nu:Measure (R3×R3) := m.prod m
  letI:IsFiniteMeasure m := isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:R3) B).measure_lt_top.ne
  letI:IsFiniteMeasure nu := by dsimp only [nu];infer_instance
  let Z:ℝ≥0∞ := nu univ ^ ((2:ℝ≥0∞).toReal⁻¹)
  have hZ:Z≠(⊤:ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top nu univ)
  refine ⟨Z.toReal+1,by positivity,?_⟩
  intro A V hA hV hAb hVb F hF M hM hBound
  have hAeMem:∀ᵐ z∂(((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)),z∈A×ˢV := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hA.prod hV)
  have hAeBound:∀ᵐ z∂(((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)),‖F z‖ ≤ M :=
    hAeMem.mono fun z hz => hBound z hz
  have hMeasure:((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V) ≤ nu :=
    Measure.prod_mono (Measure.restrict_mono_set _ hAb) (Measure.restrict_mono_set _ hVb)
  have hElp:eLpNorm F 2 (((volume:Measure R3).restrict A).prod ((volume:Measure R3).restrict V)) ≤ Z*ENNReal.ofReal M := by
    have h:=eLpNorm_le_of_ae_bound (p:=2) hF.aestronglyMeasurable hAeBound
    refine h.trans ?_
    dsimp only [Z]
    gcongr
  have hFin:Z*ENNReal.ofReal M≠(⊤:ℝ≥0∞) := ENNReal.mul_ne_top hZ ENNReal.ofReal_ne_top
  rw [Lp.norm_toLp]
  calc
    _ ≤ (Z*ENNReal.ofReal M).toReal := ENNReal.toReal_mono hFin hElp
    _ = Z.toReal*M := by rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hM]
    _ ≤ (Z.toReal+1)*M := by nlinarith only [hM]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
