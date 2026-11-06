import Calderon.SmoothHarmonicNativeWeak
import TauCeti.Analysis.PDE.Caccioppoli.Basic

/-! Exact SAME classical Caccioppoli using prescribed COMMON ellipticity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon
open TauCeti TauCeti.PDE EnergyBridge

theorem setIntegral_sq_mul_norm_gradient_sq_le_of_harmonic
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    {alpha Lambda : ℝ}
    (hell : UniformlyEllipticOn (ballOpens : Set R3) A alpha Lambda)
    {R : ℝ} (hR : 1 < R) {u : R3 → ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball (0 : R3) R))
    (heq : ∀ x ∈ (ballOpens : Set R3), divCoeffGrad A u x = 0)
    {eta : R3 → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hetac : HasCompactSupport eta) (hets : tsupport eta ⊆ (ballOpens : Set R3)) :
    (∫ x in (ballOpens : Set R3), eta x ^ 2 * ‖gradient u x‖ ^ 2) ≤
      (2 * Lambda / alpha) ^ 2 *
        ∫ x in (ballOpens : Set R3), ‖gradient eta x‖ ^ 2 * u x ^ 2 := by
  obtain ⟨v, hvalue, hgradient, _htest, henergy⟩ :=
    exists_native_weak_solution_of_contDiffOn hA hR hu heq
  have hweak : ∀ V : W1p0 (volume : Measure R3) ballOpens 2,
      energyFormH1 A 0 0 v (V : W1p (volume : Measure R3) ballOpens 2) =
        ∫ x in (ballOpens : Set R3),
          (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x *
            W1p.value (V : W1p (volume : Measure R3) ballOpens 2) x := by
    intro V
    rw [henergy V]
    symm
    exact integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
      simp only [hx, Pi.zero_apply, zero_mul])
  have hc := hell.setIntegral_sq_mul_norm_gradient_sq_le
    (mu := (volume : Measure R3))
    (f := (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)))
    hA.continuous.aestronglyMeasurable hweak heta hetac hets
  have hzero : (∫ x in (ballOpens : Set R3), eta x ^ 2 *
      (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x * W1p.value v x) = 0 :=
    integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
      simp only [hx, Pi.zero_apply, mul_zero, zero_mul])
  rw [hzero, mul_zero, add_zero] at hc
  have hleft : (∫ x in (ballOpens : Set R3), eta x ^ 2 * ‖W1p.gradient v x‖ ^ 2) =
      ∫ x in (ballOpens : Set R3), eta x ^ 2 * ‖gradient u x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hgradient] with x hx
    rw [hx]
  have hright : (∫ x in (ballOpens : Set R3), ‖gradient eta x‖ ^ 2 * W1p.value v x ^ 2) =
      ∫ x in (ballOpens : Set R3), ‖gradient eta x‖ ^ 2 * u x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hvalue] with x hx
    rw [hx]
  rw [hleft, hright] at hc
  exact hc

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.setIntegral_sq_mul_norm_gradient_sq_le_of_harmonic
