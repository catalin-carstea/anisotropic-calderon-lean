import Calderon.SmoothSobolevBridge
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! EXPANSION.json precedes this narrow squared-difference L2 limit primitive. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.EnergyBridge

theorem tendsto_Lp_two_of_dominated_squared_difference
    {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V] (μ : Measure α)
    (F : ℕ → Lp V 2 μ) (f : Lp V 2 μ) (b : α → ℝ) (hb : Integrable b μ)
    (hBound : ∀ n, ∀ᵐ x ∂μ, ‖(F n - f) x‖ ^ 2 ≤ b x)
    (hPointwise : ∀ᵐ x ∂μ,
      Tendsto (fun n => ‖(F n - f) x‖ ^ 2) atTop (𝓝 (0 : ℝ))) :
    Tendsto F atTop (𝓝 f) := by
  have hInt : Tendsto (fun n => ∫ x, ‖(F n - f) x‖ ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero,Pi.pow_apply] using
      (tendsto_integral_of_dominated_convergence (f := fun _ : α => (0 : ℝ)) b
        (fun n => (Lp.aestronglyMeasurable (F n - f)).norm.pow 2) hb
        (fun n => (hBound n).mono (fun x hx => by
          simp only [Pi.pow_apply,Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg (‖(F n - f) x‖ : ℝ))]
          exact hx)) hPointwise)
  have hSq : Tendsto (fun n => ‖F n - f‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Lp.integral_norm_sq_eq_norm_sq] using hInt
  have hRoot : ∀ n, Real.sqrt (‖F n - f‖ ^ 2) = ‖F n - f‖ :=
    fun n => Real.sqrt_sq (norm_nonneg (F n - f))
  have hNorm : Tendsto (fun n => ‖F n - f‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,hRoot,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hSq
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hNorm

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tendsto_Lp_two_of_dominated_squared_difference
