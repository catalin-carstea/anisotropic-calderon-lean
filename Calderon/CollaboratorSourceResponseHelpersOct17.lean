import Calderon.SourceRungeLiteratureInterfaces
import Calderon.CollaboratorRungeL2Oct17
import Calderon.CollaboratorInteriorEstimateOct17
import Calderon.CollaboratorDilationCorrectionEqOct17
import Calderon.MetricSmooth
import Calderon.CollaboratorBallTopologyOct17

/-! Shared original source-response/weak-restriction exports for the direct L² jet route.
The generic H5 Runge theorem and DC.main are not imported or asserted here. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource.Literature
open EnergyBridge DirichletFamily MetricVolume TauCeti TauCeti.PDE Regularity
open _root_.OAI.AnisotropicCalderon.Affine

section Generic

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- The `H¹` energy form (no drift, no mass) as an explicit integral. -/
theorem energyFormH1_zero_zero_eq_integral (u v : W1p mu Omega 2) :
    energyFormH1 a 0 0 u v = ∫ x in Omega,
      matrixBilinearForm (a x) (W1p.gradient v x) (W1p.gradient u x) ∂mu := by
  rw [energyFormH1_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [energyIntegrand_apply]

end Generic

/-- The native radius-two source solution in the integral form used by `l2_runge`. -/
theorem radiusTwoSourceSolution_integral (g : MatrixField) (hg : IsAdmissibleMetric g)
    (F : SmoothData) (φ : W1p (volume : Measure R3) radiusTwoOpens 2)
    (hφ : φ ∈ w1p0Submodule (volume : Measure R3) radiusTwoOpens 2) :
    ∫ x in ball (0 : R3) 2, matrixBilinearForm (principalCoefficient g x) (W1p.gradient φ x)
        (W1p.gradient (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing F) : RadiusTwoH1) x) =
      ∫ x in ball (0 : R3) 2, F.1 x * W1p.value φ x := by
  have h := radiusTwoSourceSolution_smooth_equation g hg F ⟨φ, hφ⟩
  rw [energyFormH1_zero_zero_eq_integral] at h
  exact h



open RungeAux in
/-- Restricting a weak solution (against tests) to a smaller open set gives a weak solution. -/
theorem restrict_weak_zero {V Ω : Opens R3} (hV : V ≤ Ω) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    {w : W1p (volume : Measure R3) Ω 2}
    (hw : ∀ ψ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set R3),
      matrixBilinearForm (A x) (gradient (ψ : R3 → ℝ) x) (W1p.gradient w x) = 0)
    (φ : 𝓓(V, ℝ)) : ∫ x in (V : Set R3),
      matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient (W1p.restrictL hV w) x)
        = 0 := by
  rw [← integral_mono_test hV A w φ, ← hw (TestFunction.monoCLM ℝ φ)]
  refine integral_congr_ae ?_
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
    (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))] with x hx
  rw [W1p.gradient_ofTestFunctionₗ, hx]

open RungeAux in
/-- The weak form is linear in the solution: difference of two weak solutions on a ball. -/
theorem sub_weak_zero (c : R3) (ρ : ℝ) {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A)
    {w₁ w₂ : W1p (volume : Measure R3) (ballO c ρ) 2}
    (h₁ : ∀ φ : 𝓓(ballO c ρ, ℝ), ∫ x in ball c ρ,
      matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w₁ x) = 0)
    (h₂ : ∀ φ : 𝓓(ballO c ρ, ℝ), ∫ x in ball c ρ,
      matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w₂ x) = 0)
    (φ : 𝓓(ballO c ρ, ℝ)) : ∫ x in ball c ρ,
      matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient (w₁ - w₂) x) = 0 := by
  obtain ⟨C, hC⟩ := exists_norm_mvA_le hA c ρ
  have hg := gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3))
    (Omega := ballO c ρ) 2 φ
  have hi : ∀ w : W1p (volume : Measure R3) (ballO c ρ) 2, Integrable
      (fun x => matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w x))
      ((volume : Measure R3).restrict (ball c ρ)) := fun w =>
    (integrable_mbf (Ω := ballO c ρ) hA hC (W1p.gradient w)
      (gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ)).congr
      (by filter_upwards [hg] with x hx; rw [hx])
  have hsub : W1p.gradient (w₁ - w₂) = W1p.gradient w₁ - W1p.gradient w₂ := by
    simp only [← W1p.gradientL_apply, map_sub]
  calc ∫ x in ball c ρ, matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient (w₁ - w₂) x)
      = ∫ x in ball c ρ, (matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w₁ x)
          - matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w₂ x)) := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (W1p.gradient w₁) (W1p.gradient w₂)] with x hx
        rw [hsub, hx, Pi.sub_apply, map_sub]
    _ = 0 := by rw [integral_sub (hi w₁) (hi w₂), h₁ φ, h₂ φ, sub_zero]


theorem nativeMetricDifferential_eq (g : MatrixField) (u : R3 → ℝ) (x : R3) :
    nativeMetricDifferential g u x = -divCoeffGrad (principalCoefficient g) u x := rfl

/-- The source response as a `W^{1,2}(ball 0 2)` element. -/
@[inline, reducible]
def Kresp (g : MatrixField) (hg : IsAdmissibleMetric g) (f : 𝓓(fixedExteriorSourceOpens, ℝ)) :
    W1p (volume : Measure R3) (ballO 0 2) 2 :=
  (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing ⟨(f : R3 → ℝ), f.contDiff⟩) : RadiusTwoH1)

end OAI.AnisotropicCalderon.ExteriorSource.Literature
