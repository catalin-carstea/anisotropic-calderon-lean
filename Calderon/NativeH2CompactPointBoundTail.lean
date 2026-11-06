import Calderon.NativeSixMorreyValueAgreement

/-! EXPANSION.json precedes the genuine quantitative compact-H2 point bound. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open MetricVolume
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((6 : NNReal) : ENNReal)) := ⟨by
  rw [ENNReal.coe_ofNat]
  norm_num⟩

theorem exists_bounded_continuous_representative_of_nativeCompactH2
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0) :
    ∃ F : R3 → ℝ, Continuous F ∧
      ((TauCeti.Wkp.value 2 U : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens] F) ∧
      ∀ x : R3, |F x| ≤ ‖nativeSixMorreyL‖ *
        (SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
          ‖TauCeti.Wkp.firstOrder 1 U‖ +
          ∑ i : Fin 3, ‖coordinateVector i‖ *
            (SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
              (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖U‖))) := by
  obtain ⟨v,hv,hg,hvBound⟩ := exists_bounded_nativeW1pSix_of_compactH2 hcalc U K hK hKB hU
  have hvK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value v x = 0 := by
    filter_upwards [hv,hU] with x hx hux hxK
    exact hx.trans (by simpa only [TauCeti.Wkp.value_firstOrder] using hux hxK)
  have hv0 : v ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 6 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hvK
  let z : TauCeti.W1p0 (volume : Measure R3) ballOpens 6 := ⟨v,hv0⟩
  let w : TauCeti.W1p (volume : Measure R3) ⊤ 6 :=
    (TauCeti.W1p0.extendByZeroL (Omega := ballOpens) (Omega' := ⊤) le_top z :
      TauCeti.W1p (volume : Measure R3) ⊤ 6)
  let H := nativeSixMorreyL w
  have hRep : (TauCeti.W1p.value w : R3 → ℝ) =ᵐ[(volume : Measure R3)] (H : R3 → ℝ) :=
    nativeSixMorreyL_value_ae w
  have hExt : (TauCeti.W1p.value w : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      (ballOpens : Set R3).indicator (TauCeti.W1p.value v) := by
    dsimp only [w]
    rw [TauCeti.W1p0.value_extendByZeroL]
    simpa only [Opens.coe_top,Measure.restrict_univ] using
      TauCeti.coeFn_extendByZeroLpₗᵢ ℝ ballOpens.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : ballOpens ≤ (⊤ : Opens R3))) (TauCeti.W1p.value v)
  have hRepB : (TauCeti.W1p.value w : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens] (H : R3 → ℝ) := ae_restrict_of_ae hRep
  have hExtB : (TauCeti.W1p.value w : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
        (ballOpens : Set R3).indicator (TauCeti.W1p.value v) := ae_restrict_of_ae hExt
  have hNorm : ‖w‖ = ‖v‖ := TauCeti.W1p0.norm_extendByZeroL le_top z
  refine ⟨(H : R3 → ℝ),H.continuous,?_,?_⟩
  · filter_upwards [hRepB,hExtB,hv,ae_restrict_mem ballOpens.isOpen.measurableSet]
      with x hx he hvx hxB
    have hOld : TauCeti.W1p.value (TauCeti.Wkp.firstOrder 1 U) x = TauCeti.Wkp.value 2 U x :=
      congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x) (TauCeti.Wkp.value_firstOrder 1 U)
    have he' : TauCeti.W1p.value w x = TauCeti.W1p.value v x := by
      simpa only [indicator_of_mem hxB] using he
    exact hOld.symm.trans (hvx.symm.trans (he'.symm.trans hx))
  · intro x
    have hp : |H x| ≤ ‖H‖ := by
      have hPoint := H.toBoundedContinuousFunction.norm_coe_le_norm x
      rw [TauCeti.HolderSpace.toBoundedContinuousFunction_apply] at hPoint
      have hBound : ‖H.toBoundedContinuousFunction‖ ≤ ‖H‖ := H.norm_toBoundedContinuousFunction_le
      calc
        |H x| = ‖H x‖ := (Real.norm_eq_abs (H x)).symm
        _ ≤ ‖H.toBoundedContinuousFunction‖ := hPoint
        _ ≤ ‖H‖ := hBound
    exact hp.trans ((nativeSixMorreyL.le_opNorm w).trans
      (mul_le_mul_of_nonneg_left (by rw [hNorm]; exact hvBound) (norm_nonneg _)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
