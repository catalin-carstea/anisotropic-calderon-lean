import Calderon.RadiusTwoLpDilationBound
import Calderon.NativeH1InwardDilation

/-! Full EXPANSION.json precedes this focused partition of original nativezero dilation5. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal Distributions ContDiff Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

theorem norm_nativeZeroTestPullback_le_three (phi : 𝓓(radiusTwoOpens, ℝ)) :
    ‖nativeZeroTestLinear ballOpens (radiusTwoTestPullback phi)‖ ≤
      3 * ‖nativeZeroTestLinear radiusTwoOpens phi‖ := by
  let u : RadiusTwoH1 := TauCeti.W1p.ofTestFunctionₗ volume radiusTwoOpens 2 phi
  let v : BallH1 := TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2
    (radiusTwoTestPullback phi)
  have hValue : eLpNorm (phi : R3 → ℝ) 2
      ((volume : Measure R3).restrict radiusTwoOpens) ≠ ⊤ := by
    rw [← eLpNorm_congr_ae (TauCeti.testFunctionLp_apply_ae (mu := volume) 2 phi)]
    exact (Lp.memLp (TauCeti.testFunctionLp (mu := volume) 2 phi)).eLpNorm_ne_top
  have hv : ‖TauCeti.W1p.value v‖ ≤ ‖TauCeti.W1p.value u‖ := by
    have ht := ENNReal.toReal_mono hValue (eLpNorm_unit_comp_two_le_radiusTwo (phi : R3 → ℝ))
    rw [Lp.norm_def,Lp.norm_def,TauCeti.W1p.value_ofTestFunctionₗ,
      TauCeti.W1p.value_ofTestFunctionₗ,
      eLpNorm_congr_ae (TauCeti.testFunctionLp_apply_ae (mu := volume) 2
        (radiusTwoTestPullback phi)),
      eLpNorm_congr_ae (TauCeti.testFunctionLp_apply_ae (mu := volume) 2 phi)]
    exact ht
  have hGradient : (TauCeti.W1p.gradient v : R3 → R3)
      =ᵐ[(volume : Measure R3).restrict ballOpens]
        (fun x : R3 => (2 : ℝ) • gradient (phi : R3 → ℝ) ((2 : ℝ) • x)) := by
    dsimp only [v]
    rw [TauCeti.W1p.gradient_ofTestFunctionₗ]
    filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2
      (radiusTwoTestPullback phi)] with x hx
    rw [hx]
    exact gradient_comp_const_smul (phi : R3 → ℝ) 2 x
      (phi.contDiff.differentiable (by simp) ((2 : ℝ) • x))
  have hGN : eLpNorm (gradient (phi : R3 → ℝ)) 2
      ((volume : Measure R3).restrict radiusTwoOpens) ≠ ⊤ := by
    rw [← eLpNorm_congr_ae (TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 phi)]
    exact (Lp.memLp (TauCeti.gradientTestFunctionLp (mu := volume) 2 phi)).eLpNorm_ne_top
  have hg : ‖TauCeti.W1p.gradient v‖ ≤ 2 * ‖TauCeti.W1p.gradient u‖ := by
    have he : eLpNorm (fun x : R3 => (2 : ℝ) • gradient (phi : R3 → ℝ) ((2 : ℝ) • x)) 2
        ((volume : Measure R3).restrict ballOpens) ≤
      2 * eLpNorm (gradient (phi : R3 → ℝ)) 2
        ((volume : Measure R3).restrict radiusTwoOpens) := by
      have hScale : eLpNorm (fun x : R3 => (2 : ℝ) • gradient (phi : R3 → ℝ) ((2 : ℝ) • x)) 2
          ((volume : Measure R3).restrict ballOpens) =
            ‖(2 : ℝ)‖ₑ * eLpNorm (fun x : R3 => gradient (phi : R3 → ℝ) ((2 : ℝ) • x)) 2
              ((volume : Measure R3).restrict ballOpens) :=
        eLpNorm_const_smul (2 : ℝ) (fun x : R3 => gradient (phi : R3 → ℝ) ((2 : ℝ) • x)) 2
          ((volume : Measure R3).restrict ballOpens)
      rw [hScale]
      have hnorm : ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) := by
        rw [← ofReal_norm (2 : ℝ),Real.norm_eq_abs]
        norm_num
      rw [hnorm]
      exact mul_le_mul' le_rfl (eLpNorm_unit_comp_two_le_radiusTwo (gradient (phi : R3 → ℝ)))
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hGN) he
    rw [Lp.norm_def,Lp.norm_def,eLpNorm_congr_ae hGradient,
      TauCeti.W1p.gradient_ofTestFunctionₗ,
      eLpNorm_congr_ae (TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 phi)]
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] using ht
  change ‖v‖ ≤ 3 * ‖u‖
  calc
    ‖v‖ ≤ ‖TauCeti.W1p.value v‖ + ‖TauCeti.W1p.gradient v‖ :=
      TauCeti.W1p.norm_le_norm_value_add_norm_gradient v
    _ ≤ ‖TauCeti.W1p.value u‖ + 2 * ‖TauCeti.W1p.gradient u‖ := add_le_add hv hg
    _ ≤ ‖u‖ + 2 * ‖u‖ := add_le_add (TauCeti.W1p.norm_value_le u)
      (mul_le_mul_of_nonneg_left (TauCeti.W1p.norm_gradient_le u) (by norm_num))
    _ = 3 * ‖u‖ := by ring

end OAI.AnisotropicCalderon.ExteriorSource
