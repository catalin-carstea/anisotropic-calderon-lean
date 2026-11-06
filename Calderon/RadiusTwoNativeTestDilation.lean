import Calderon.RadiusTwoNativeSourceFoundation
import Mathlib.Topology.Algebra.Support

/-! EXPANSION.json precedes this actual zero-space/test-dilation prerequisite.
No native carrier transport or Green-kernel premise is assumed here. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal Distributions ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

def nativeZeroTestLinear (Omega : Opens R3) :
    𝓓(Omega, ℝ) →ₗ[ℝ] TauCeti.W1p0 (volume : Measure R3) Omega 2 :=
  (TauCeti.W1p.ofTestFunctionₗ (volume : Measure R3) Omega 2).codRestrict
    (TauCeti.w1p0Submodule (volume : Measure R3) Omega 2).toSubmodule
    (TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule)

theorem nativeZeroTestLinear_coe (Omega : Opens R3) (phi : 𝓓(Omega, ℝ)) :
    (nativeZeroTestLinear Omega phi : TauCeti.W1p (volume : Measure R3) Omega 2) =
      TauCeti.W1p.ofTestFunctionₗ (volume : Measure R3) Omega 2 phi := rfl

theorem denseRange_nativeZeroTestLinear (Omega : Opens R3) :
    DenseRange (nativeZeroTestLinear Omega) := by
  intro u
  rw [closure_subtype, ← Set.range_comp]
  have hu : (u : TauCeti.W1p (volume : Measure R3) Omega 2) ∈
      (TauCeti.w1p0Submodule (volume : Measure R3) Omega 2 :
        Set (TauCeti.W1p (volume : Measure R3) Omega 2)) := u.2
  rw [TauCeti.coe_w1p0Submodule] at hu
  simpa only [Function.comp_def, nativeZeroTestLinear_coe] using hu

def radiusTwoTestPullback (phi : 𝓓(radiusTwoOpens, ℝ)) : 𝓓(ballOpens, ℝ) where
  toFun x := phi ((2 : ℝ) • x)
  contDiff' := phi.contDiff.comp ((2 : ℝ) • ContinuousLinearMap.id ℝ R3).contDiff
  hasCompactSupport' := by
    let h : R3 ≃ₜ R3 := Homeomorph.smul (Units.mk0 (2 : ℝ) (by norm_num))
    exact phi.hasCompactSupport.comp_homeomorph h
  tsupport_subset' := by
    intro x hx
    have htwo : (2 : ℝ) • x ∈ tsupport (phi : R3 → ℝ) :=
      tsupport_comp_subset_preimage (f := fun y : R3 => (2 : ℝ) • y)
        (phi : R3 → ℝ) (by fun_prop) hx
    have houter : (2 : ℝ) • x ∈ ball (0 : R3) (2 : ℝ) := phi.tsupport_subset htwo
    have hn : ‖(2 : ℝ) • x‖ < 2 := by
      simpa only [mem_ball, dist_zero_right] using houter
    rw [norm_smul, Real.norm_eq_abs] at hn
    norm_num at hn
    change x ∈ ball (0 : R3) 1
    rw [mem_ball, dist_zero_right]
    linarith

theorem radiusTwoTestPullback_apply (phi : 𝓓(radiusTwoOpens, ℝ)) (x : R3) :
    radiusTwoTestPullback phi x = phi ((2 : ℝ) • x) := rfl

def radiusTwoTestPullbackLinear : 𝓓(radiusTwoOpens, ℝ) →ₗ[ℝ] 𝓓(ballOpens, ℝ) where
  toFun := radiusTwoTestPullback
  map_add' phi psi := by
    ext x
    rfl
  map_smul' c phi := by
    ext x
    rfl

end OAI.AnisotropicCalderon.ExteriorSource
