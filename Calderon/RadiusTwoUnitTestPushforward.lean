import Calderon.RadiusTwoNativeTestDilation

/-! Full EXPANSION.json precedes the literal inverse pullback on compact tests. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric TopologicalSpace
open scoped Distributions ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge

def radiusTwoUnitTestPushforward (phi : 𝓓(ballOpens, ℝ)) : 𝓓(radiusTwoOpens, ℝ) where
  toFun z := phi ((1/2 : ℝ) • z)
  contDiff' := phi.contDiff.comp ((1/2 : ℝ) • ContinuousLinearMap.id ℝ R3).contDiff
  hasCompactSupport' := by
    let h : R3 ≃ₜ R3 := Homeomorph.smul (Units.mk0 (1/2 : ℝ) (by norm_num))
    exact phi.hasCompactSupport.comp_homeomorph h
  tsupport_subset' := by
    intro z hz
    have hhalf : (1/2 : ℝ) • z ∈ tsupport (phi : R3 → ℝ) :=
      tsupport_comp_subset_preimage (f := fun y : R3 => (1/2 : ℝ) • y)
        (phi : R3 → ℝ) (by fun_prop) hz
    have hinner : (1/2 : ℝ) • z ∈ ball (0 : R3) (1 : ℝ) := phi.tsupport_subset hhalf
    have hn : ‖(1/2 : ℝ) • z‖ < 1 := by
      simpa only [mem_ball,dist_zero_right] using hinner
    rw [norm_smul,Real.norm_eq_abs] at hn
    norm_num at hn
    change z ∈ ball (0 : R3) 2
    rw [mem_ball,dist_zero_right]
    linarith

theorem radiusTwoUnitTestPushforward_apply (phi : 𝓓(ballOpens, ℝ)) (z : R3) :
    radiusTwoUnitTestPushforward phi z = phi ((1/2 : ℝ) • z) := rfl

theorem radiusTwoTestPullback_unitTestPushforward (phi : 𝓓(ballOpens, ℝ)) :
    radiusTwoTestPullback (radiusTwoUnitTestPushforward phi) = phi := by
  ext x
  change phi ((1/2 : ℝ) • ((2 : ℝ) • x)) = phi x
  rw [smul_smul]
  norm_num

end OAI.AnisotropicCalderon.ExteriorSource
