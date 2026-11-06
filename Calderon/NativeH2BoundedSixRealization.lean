import Calderon.NativeH2SixVectorBound

/-! EXPANSION.json precedes this bounded actual W1p6 realization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open MetricVolume
open EnergyBridge
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem exists_bounded_nativeW1pSix_of_compactH2
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0) :
    ∃ v : TauCeti.W1p (volume : Measure R3) ballOpens 6,
      ((TauCeti.W1p.value v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
        TauCeti.W1p.value (TauCeti.Wkp.firstOrder 1 U)) ∧
      ((TauCeti.W1p.gradient v : R3 → R3) =ᵐ[(volume : Measure R3).restrict ballOpens]
        TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U)) ∧
      ‖v‖ ≤ SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
        ‖TauCeti.Wkp.firstOrder 1 U‖ +
        ∑ i : Fin 3, ‖coordinateVector i‖ *
          (SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
            (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖U‖)) := by
  obtain ⟨v,hv,hg⟩ := exists_nativeW1pSix_of_compactH2 hcalc U K hK hKB hU
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  have hu : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value u x = 0 := by
    simpa only [u,TauCeti.Wkp.value_firstOrder] using hU
  have hu0 : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hu
  have hValue : TauCeti.W1p.value v =
      (memLp_nativeH1_value_six_of_zero u hu0).toLp (TauCeti.W1p.value u) := by
    apply Lp.ext
    filter_upwards [hv,MemLp.coeFn_toLp (memLp_nativeH1_value_six_of_zero u hu0)]
      with x hx hto
    exact hx.trans hto.symm
  have hGradient : TauCeti.W1p.gradient v =
      (memLp_nativeCompactH2_gradient_six hcalc U K hK hKB hU).toLp
        (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U)) := by
    apply Lp.ext
    filter_upwards [hg,MemLp.coeFn_toLp (memLp_nativeCompactH2_gradient_six hcalc U K hK hKB hU)]
      with x hx hto
    exact hx.trans hto.symm
  refine ⟨v,hv,hg,?_⟩
  refine (TauCeti.W1p.norm_le_norm_value_add_norm_gradient v).trans ?_
  rw [hValue,hGradient]
  exact add_le_add (norm_nativeH1_value_six_of_zero_le u hu0)
    (norm_nativeCompactH2_gradient_six_le hcalc U K hK hKB hU)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
