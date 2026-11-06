import Calderon.NativeInteriorH2ContinuousRepresentative

/-! EXPANSION.json precedes the quantitative native scalar L6 estimates. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem norm_nativeH1_value_six_of_zero_le
    (u : BallH1) (hu : u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) :
    ‖(memLp_nativeH1_value_six_of_zero u hu).toLp (TauCeti.W1p.value u)‖ ≤
      SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal * ‖u‖ := by
  have hexp : (6 : ℝ≥0∞)⁻¹ + (Module.finrank ℝ R3 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    have hDim : Module.finrank ℝ R3 = 3 := by simp [R3]
    rw [hDim]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num [ENNReal.toReal_inv]
  have hNorm : ‖(memLp_nativeH1_value_six_of_zero u hu).toLp (TauCeti.W1p.value u)‖ ≤
      SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
        ‖TauCeti.W1p.gradient u‖ := by
    rw [Lp.norm_toLp]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (TauCeti.W1p.eLpNorm_value_le_mul_enorm_gradient
      (show (6 : ℝ≥0∞) ≠ ∞ by norm_num) hexp hu).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_coe_nnreal,ofReal_norm]
  exact hNorm.trans (mul_le_mul_of_nonneg_left (TauCeti.W1p.norm_gradient_le u)
    (NNReal.coe_nonneg _))

theorem norm_nativeCompactH2_gradient_coordinate_six_le
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 2) (K : Set R3)
    (hK : IsCompact K) (hKB : K ⊆ (ballOpens : Set R3))
    (hU : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.Wkp.value 2 U x = 0)
    (i : Fin 3) :
    ‖(memLp_nativeCompactH2_gradient_coordinate_six hcalc U K hK hKB hU i).toLp
      (fun x : R3 => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i)‖ ≤
      SNormLESNormFDerivOfEqConst ℝ (volume : Measure R3) (2 : ℝ≥0∞).toReal *
        (‖unitBallCoordinateDerivativeL hcalc 1 i‖ * ‖U‖) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  let d : BallH1 := unitBallCoordinateDerivativeL hcalc 1 i U
  have hu : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value u x = 0 := by
    simpa only [u,TauCeti.Wkp.value_firstOrder] using hU
  have hg := nativeH1_gradient_ae_zero_off_compact u K hK hu
  have hd : (TauCeti.W1p.value d : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x : R3 => (TauCeti.W1p.gradient u x) i) := by
    simpa only [d,u,TauCeti.Wkp.value_one] using unitBallCoordinateDerivativeL_value_ae hcalc 1 i U
  have hdK : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∉ K → TauCeti.W1p.value d x = 0 := by
    filter_upwards [hd,hg] with x hx hgrad hxK
    exact hx.trans (congrArg (fun z : R3 => z i) (hgrad hxK))
  have hd0 : d ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    TauCeti.W1p.mem_w1p0Submodule_of_isCompact (by norm_num) hK hKB hdK
  have hEq : ‖(memLp_nativeCompactH2_gradient_coordinate_six hcalc U K hK hKB hU i).toLp
      (fun x : R3 => (TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 1 U) x) i)‖ =
        ‖(memLp_nativeH1_value_six_of_zero d hd0).toLp (TauCeti.W1p.value d)‖ := by
    rw [Lp.norm_toLp,Lp.norm_toLp]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hd.symm)
  rw [hEq]
  exact (norm_nativeH1_value_six_of_zero_le d hd0).trans
    (mul_le_mul_of_nonneg_left ((unitBallCoordinateDerivativeL hcalc 1 i).le_opNorm U)
      (NNReal.coe_nonneg _))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
