import Calderon.CollaboratorSourceJetWeakEstimatesOct17
import Calderon.CollaboratorDilationCorrectionEqOct17

/-! Exact SAME smooth solution to native weak energy witness for Main M1. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon
open TauCeti TauCeti.PDE EnergyBridge

theorem exists_native_weak_solution_of_contDiffOn
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    {R : ℝ} (hR : 1 < R) {u : R3 → ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball (0 : R3) R))
    (heq : ∀ x ∈ (ballOpens : Set R3), divCoeffGrad A u x = 0) :
    ∃ v : W1p (volume : Measure R3) ballOpens 2,
      ⇑(W1p.value v) =ᵐ[(volume : Measure R3).restrict ballOpens] u ∧
      ⇑(W1p.gradient v) =ᵐ[(volume : Measure R3).restrict ballOpens] ∇ u ∧
      (∀ phi : 𝓓(ballOpens, ℝ),
        ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x)
          (gradient (phi : R3 → ℝ) x) (W1p.gradient v x) = 0) ∧
      (∀ V : W1p0 (volume : Measure R3) ballOpens 2,
        energyFormH1 A 0 0 v (V : W1p (volume : Measure R3) ballOpens 2) = 0) := by
  obtain ⟨v, hv⟩ : ∃ v : W1p (volume : Measure R3) ballOpens 2,
      ⇑(W1p.value v) =ᵐ[(volume : Measure R3).restrict ballOpens] u := by
    have hwitness := ExteriorSource.Literature.JetsAsm.exists_w1p_of_contDiffOn
      (p := (0 : R3)) (ρ₁ := 1) (by norm_num) hR hu
    change ∃ v : W1p (volume : Measure R3) ballOpens 2,
      ⇑(W1p.value v) =ᵐ[(volume : Measure R3).restrict ballOpens] u at hwitness
    exact hwitness
  have hu1 : ContDiffOn ℝ ∞ u (ball (0 : R3) 1) :=
    hu.mono (ball_subset_ball hR.le)
  have hgrad : ⇑(W1p.gradient v) =ᵐ[(volume : Measure R3).restrict ballOpens] ∇ u :=
    Regularity.IS.gradient_ae_eq v hu1 hv
  have htest : ∀ phi : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x)
        (gradient (phi : R3 → ℝ) x) (W1p.gradient v x) = 0 := by
    intro phi
    exact Regularity.DC.weak_of_classical (0 : R3) (by norm_num : 0 < (1 : ℝ))
      hA v hu1 hv heq phi
  have htest0 : ∀ phi : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x)
        (gradient (phi : R3 → ℝ) x) (W1p.gradient v x) =
      ∫ x in (ballOpens : Set R3),
        (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x * phi x := by
    intro phi
    rw [htest phi]
    symm
    exact integral_eq_zero_of_ae (by
      filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
      simp only [hx, Pi.zero_apply, zero_mul])
  refine ⟨v, hv, hgrad, htest, ?_⟩
  intro V
  have henergy : energyFormH1 A 0 0 v
      (V : W1p (volume : Measure R3) ballOpens 2) =
      ∫ x in (ballOpens : Set R3),
        (0 : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) x *
          W1p.value (V : W1p (volume : Measure R3) ballOpens 2) x := by
    rw [energyFormH1_def, ← Regularity.eq_of_testFunction hA.continuous htest0 _ V.2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [energyIntegrand_apply]
  rw [henergy]
  exact integral_eq_zero_of_ae (by
    filter_upwards [Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)] with x hx
    simp only [hx, Pi.zero_apply, zero_mul])

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.exists_native_weak_solution_of_contDiffOn
