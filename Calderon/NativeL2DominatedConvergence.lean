import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma tendsto_L2_of_ae_tendsto_of_norm_sub_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (f : ℕ → Lp E 2 μ) (g : Lp E 2 μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x-g x‖ ≤ ‖g x‖)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto f atTop (𝓝 g) := by
  have hdom : Integrable (fun x => ‖g x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).mp (Lp.memLp g)
  have hint : Tendsto (fun n => ∫ x, ‖f n x-g x‖^2 ∂μ) atTop (𝓝 (0:ℝ)) := by
    have hb2 : ∀ n, ∀ᵐ x ∂μ, ‖‖f n x-g x‖^2‖ ≤ ‖g x‖^2 := by
      intro n
      filter_upwards [hb n] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (f n x-g x),norm_nonneg (g x)]
    have hl2 : ∀ᵐ x ∂μ,
        Tendsto (fun n => ‖f n x-g x‖^2) atTop (𝓝 ((fun _ : X => (0:ℝ)) x)) := by
      filter_upwards [hl] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := g x))).norm.pow 2)
    have h := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖^2)
      (fun n => ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable g)).norm.pow 2)
      hdom hb2 hl2
    simpa only [Pi.sub_apply,Pi.pow_apply,integral_zero] using h
  have heq (n : ℕ) : (∫ x, ‖f n x-g x‖^2 ∂μ) = ‖f n-g‖^2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f n) g] with x hx
    exact congrArg (fun y : E => ‖y‖^2) hx.symm
  simp_rw [heq] at hint
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hint
  have he : ((fun x : ℝ => Real.sqrt x) ∘ (fun n => ‖f n-g‖^2)) =
      (fun n => ‖f n-g‖) := by
    funext n
    exact Real.sqrt_sq (norm_nonneg (f n-g))
  rw [he,Real.sqrt_zero] at h
  exact h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_L2_of_ae_tendsto_of_norm_sub_le
