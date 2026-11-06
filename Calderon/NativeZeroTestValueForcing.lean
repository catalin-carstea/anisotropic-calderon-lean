import Calderon.RadiusTwoNativeTestDilation
import TauCeti.Analysis.PDE.DirichletProblem

/-! EXPANSION.json precedes the actual native compact-test scalar projections. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Distributions InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem value_nativeZeroTestLinear_eq_testFunctionLp
    (Ω : Opens R3) (φ : 𝓓(Ω, ℝ)) :
    TauCeti.W1p.value (nativeZeroTestLinear Ω φ : TauCeti.W1p (volume : Measure R3) Ω 2) =
      TauCeti.testFunctionLp (mu := (volume : Measure R3)) 2 φ := by
  rw [nativeZeroTestLinear_coe,TauCeti.W1p.value_ofTestFunctionₗ]

theorem value_nativeZeroTestLinear_ae
    (Ω : Opens R3) (φ : 𝓓(Ω, ℝ)) :
    (TauCeti.W1p.value (nativeZeroTestLinear Ω φ : TauCeti.W1p (volume : Measure R3) Ω 2) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict Ω] (φ : R3 → ℝ) := by
  filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ] with x hx
  exact (congrArg (fun v : Lp ℝ 2 ((volume : Measure R3).restrict Ω) => (v : R3 → ℝ) x)
    (value_nativeZeroTestLinear_eq_testFunctionLp Ω φ)).trans hx

theorem dirichletForcing_nativeZeroTest_eq_integral
    (Ω : Opens R3) (f : Lp ℝ 2 ((volume : Measure R3).restrict Ω)) (φ : 𝓓(Ω, ℝ)) :
    TauCeti.PDE.dirichletForcing f (nativeZeroTestLinear Ω φ) =
      ∫ x in Ω, f x * φ x ∂(volume : Measure R3) := by
  apply (TauCeti.PDE.dirichletForcing_apply_eq_setIntegral f (nativeZeroTestLinear Ω φ)).trans
  apply integral_congr_ae
  filter_upwards [value_nativeZeroTestLinear_ae Ω φ] with x hx
  exact congrArg (fun r : ℝ => f x*r) hx

theorem integral_smul_Lp_mul_nativeTest
    (Ω : Opens R3) (c : ℝ) (f : Lp ℝ 2 ((volume : Measure R3).restrict Ω)) (φ : 𝓓(Ω, ℝ)) :
    (∫ x in Ω, (c • f) x * φ x ∂(volume : Measure R3)) =
      c * (∫ x in Ω, f x * φ x ∂(volume : Measure R3)) := by
  calc
    _ = ∫ x in Ω, c*(f x*φ x) ∂(volume : Measure R3) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f] with x hx
      change (c • f) x = c • f x at hx
      rw [hx]
      simp only [smul_eq_mul,mul_assoc]
    _ = _ := integral_const_mul _ _

end OAI.AnisotropicCalderon.ExteriorSource
