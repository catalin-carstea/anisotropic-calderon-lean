import Calderon.SphereHarmonicBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic

theorem norm_mul_div_sq_le_of_moment_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (chi V r C : ℝ) (w : E) (_hC : 0 ≤ C) (hr : 0 < r)
    (hMoment : |V| ≤ C * r^2 * ‖w‖) :
    ‖chi * V / r^2‖ ≤ C * ‖chi • w‖ := by
  have hr2 : 0 < r^2 := pow_pos hr 2
  have hDiv : |V| / r^2 ≤ C * ‖w‖ := by
    apply (div_le_iff₀ hr2).2
    calc
      |V| ≤ C * r^2 * ‖w‖ := hMoment
      _ = (C * ‖w‖) * r^2 := by ac_rfl
  calc
    ‖chi * V / r^2‖ = |chi| * (|V| / r^2) := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact mul_div_assoc _ _ _
    _ ≤ |chi| * (C * ‖w‖) := mul_le_mul_of_nonneg_left hDiv (abs_nonneg chi)
    _ = C * ‖chi • w‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ac_rfl

theorem memLp_weighted_source_moment_and_eLpNorm_le
    (μ : Measure R3) (chi V r : R3 → ℝ) (w : R3 → SphereL2)
    (C : ℝ) (hC : 0 ≤ C)
    (hSourceMeas : AEStronglyMeasurable (fun y => chi y * V y / (r y)^2) μ)
    (hRadius : ∀ᵐ y ∂μ, 0 < r y)
    (hMoment : ∀ᵐ y ∂μ, |V y| ≤ C * (r y)^2 * ‖w y‖)
    (hDensity : MemLp (fun y => chi y • w y) 2 μ) :
    MemLp (fun y => chi y * V y / (r y)^2) 2 μ ∧
      eLpNorm (fun y => chi y * V y / (r y)^2) 2 μ ≤
        ENNReal.ofReal C * eLpNorm (fun y => chi y • w y) 2 μ := by
  have hDomination : ∀ᵐ y ∂μ,
      ‖chi y * V y / (r y)^2‖ ≤ C * ‖chi y • w y‖ := by
    filter_upwards [hRadius, hMoment] with y hy hMomentY
    exact norm_mul_div_sq_le_of_moment_bound (chi y) (V y) (r y) C (w y) hC hy hMomentY
  exact ⟨hDensity.of_le_mul hSourceMeas hDomination,
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hSourceMeas hDomination 2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
