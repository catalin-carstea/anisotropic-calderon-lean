import Calderon.RadiusTwoNativeSourceSolution
import Calderon.RadiusTwoNativeEnergyEvaluation

/-! EXPANSION.json precedes this equation/uniqueness derivation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_bound_radiusTwoSourceSolution (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : RadiusTwoL2, ‖radiusTwoSourceSolution g hg f‖ ≤ C * ‖f‖ := by
  obtain ⟨c,hc,hLower⟩ := isCoercive_radiusTwoMetricEnergyL0Normalized g hg
  refine ⟨c⁻¹,inv_nonneg.mpr hc.le,?_⟩
  intro f
  let u : RadiusTwoH1Zero := radiusTwoSourceSolution g hg f
  have hCo : c * ‖u‖ * ‖u‖ ≤ TauCeti.PDE.dirichletForcing f u := by
    exact (hLower u).trans_eq ((radiusTwoMetricEnergyL0Normalized_apply g hg u u).trans
      (radiusTwoSourceSolution_equation g hg f u))
  have hForce : |TauCeti.PDE.dirichletForcing f u| ≤ ‖f‖ * ‖u‖ := by
    simpa only [Real.norm_eq_abs] using TauCeti.PDE.norm_dirichletForcing_apply_le f u
  have hKey : c * ‖u‖ * ‖u‖ ≤ ‖f‖ * ‖u‖ :=
    hCo.trans ((le_abs_self _).trans hForce)
  have hBound : ‖u‖ ≤ ‖f‖ / c := by
    rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hpos
    · rw [← hzero]
      exact div_nonneg (norm_nonneg f) hc.le
    · rw [le_div_iff₀ hc]
      nlinarith [hKey]
  simpa only [u,div_eq_mul_inv,mul_comm] using hBound

end OAI.AnisotropicCalderon.ExteriorSource
