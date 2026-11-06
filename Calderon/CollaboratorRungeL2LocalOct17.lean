import Calderon.CollaboratorRungeL2CoreOct17
import TauCeti.Analysis.Sobolev.W1p.Restriction

/-! Local test-function arguments for the `L²` Runge approximation `l2_runge`. -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.RungeAux
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine

/-- The matrix acting on `R3`, as a continuous linear map. -/
@[inline, reducible]
def mvA (A : Matrix (Fin 3) (Fin 3) ℝ) : R3 →L[ℝ] R3 := Matrix.toEuclideanCLM (𝕜 := ℝ) A

theorem mbf_eq_inner (A : Matrix (Fin 3) (Fin 3) ℝ) (η ξ : R3) :
    matrixBilinearForm A η ξ = ⟪η, mvA A ξ⟫_ℝ := by
  rw [matrixBilinearForm_apply, Matrix.inner_toEuclideanCLM]

theorem continuous_mvA {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A) :
    Continuous fun x => mvA (A x) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp
    hA

theorem exists_norm_mvA_le {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A) (c : R3)
    (R : ℝ) : ∃ C, ∀ x ∈ ball c R, ‖mvA (A x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    (continuous_mvA hA).continuousOn
  exact ⟨C, fun x hx => hC x (ball_subset_closedBall hx)⟩

section Open

variable {Ω : Opens R3} {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A) {C : ℝ}
  (hC : ∀ x ∈ (Ω : Set R3), ‖mvA (A x)‖ ≤ C)
include hA hC

theorem memLp_mvA (G : Lp R3 2 ((volume : Measure R3).restrict Ω)) :
    MemLp (fun x => mvA (A x) (G x)) 2 ((volume : Measure R3).restrict Ω) := by
  refine MemLp.of_le_mul (c := C) (Lp.memLp G)
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := R3) (F := R3)).continuous.comp_aestronglyMeasurable
      ((continuous_mvA hA).aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G))) ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact ((mvA (A x)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))

theorem integral_mbf_eq_inner (G g : Lp R3 2 ((volume : Measure R3).restrict Ω)) :
    ∫ x in (Ω : Set R3), matrixBilinearForm (A x) (g x) (G x) =
      ⟪g, (memLp_mvA hA hC G).toLp _⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_mvA hA hC G).coeFn_toLp] with x hx
  rw [hx, mbf_eq_inner]

theorem integrable_mbf (G g : Lp R3 2 ((volume : Measure R3).restrict Ω)) :
    Integrable (fun x => matrixBilinearForm (A x) (g x) (G x))
      ((volume : Measure R3).restrict Ω) := by
  refine (L2.integrable_inner (𝕜 := ℝ) g ((memLp_mvA hA hC G).toLp _)).congr ?_
  filter_upwards [(memLp_mvA hA hC G).coeFn_toLp] with x hx
  rw [hx, mbf_eq_inner]

omit hA hC in
theorem integral_mul_eq_inner (F f : Lp ℝ 2 ((volume : Measure R3).restrict Ω)) :
    ∫ x in (Ω : Set R3), F x * f x = ⟪f, F⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- An equation tested against test functions holds against all of `H¹₀(Ω)`. -/
theorem eq_of_test {G : Lp R3 2 ((volume : Measure R3).restrict Ω)}
    {F : Lp ℝ 2 ((volume : Measure R3).restrict Ω)}
    (htest : ∀ φ : 𝓓(Ω, ℝ),
      ∫ x in (Ω : Set R3), matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (G x) =
        ∫ x in (Ω : Set R3), F x * φ x)
    (φ : W1p (volume : Measure R3) Ω 2)
    (hφ : φ ∈ w1p0Submodule (volume : Measure R3) Ω 2) :
    ∫ x in (Ω : Set R3), matrixBilinearForm (A x) (W1p.gradient φ x) (G x) =
      ∫ x in (Ω : Set R3), F x * W1p.value φ x := by
  have hclosed : IsClosed {φ : W1p (volume : Measure R3) Ω 2 |
      ∫ x in (Ω : Set R3), matrixBilinearForm (A x) (W1p.gradient φ x) (G x) =
        ∫ x in (Ω : Set R3), F x * W1p.value φ x} := by
    simp only [integral_mbf_eq_inner hA hC, integral_mul_eq_inner]
    exact isClosed_eq (W1p.gradientL.continuous.inner continuous_const)
      (W1p.valueL.continuous.inner continuous_const)
  refine w1p0Submodule_subset_of_isClosed hclosed (fun ψ => ?_) hφ
  refine (integral_congr_ae ?_).trans ((htest ψ).trans (integral_congr_ae ?_))
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]
  · filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x hx
    rw [W1p.value_ofTestFunctionₗ, hx]

end Open

/-! ### Extension by zero and restriction of test functions -/

theorem exists_extL {U S : Set R3} (hU : MeasurableSet U) (hUS : U ⊆ S)
    (h : Lp ℝ 2 ((volume : Measure R3).restrict U)) :
    ∃ F : Lp ℝ 2 ((volume : Measure R3).restrict S),
      ∀ g : R3 → ℝ, ∫ x in S, F x * g x = ∫ x in U, h x * g x := by
  have hres : ((volume : Measure R3).restrict S).restrict U = (volume : Measure R3).restrict U := by
    rw [Measure.restrict_restrict hU, Set.inter_eq_left.2 hUS]
  have hmem : MemLp (U.indicator (h : R3 → ℝ)) 2 ((volume : Measure R3).restrict S) :=
    (memLp_indicator_iff_restrict hU.nullMeasurableSet).2 (by rw [hres]; exact Lp.memLp h)
  refine ⟨hmem.toLp _, fun g => ?_⟩
  calc ∫ x in S, (hmem.toLp _ : R3 → ℝ) x * g x
      = ∫ x in S, U.indicator (fun y => h y * g y) x := by
        refine integral_congr_ae ?_
        filter_upwards [hmem.coeFn_toLp] with x hx
        rw [hx, Set.indicator_mul_left]
    _ = ∫ x in U, h x * g x := by
        rw [integral_indicator hU, hres]

theorem gradient_eq_zero_of_notMem {V : Opens R3} (φ : 𝓓(V, ℝ)) {x : R3}
    (hx : x ∉ (V : Set R3)) : gradient (φ : R3 → ℝ) x = 0 := by
  have h : fderiv ℝ (φ : R3 → ℝ) x = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) fun h' => hx (φ.tsupport_subset h')
  simp [gradient, h]

theorem eq_zero_of_notMem {V : Opens R3} (φ : 𝓓(V, ℝ)) {x : R3}
    (hx : x ∉ (V : Set R3)) : (φ : R3 → ℝ) x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h' => hx (φ.tsupport_subset h')

theorem coe_monoCLM {V Ω : Opens R3} (hV : V ≤ Ω) (φ : 𝓓(V, ℝ)) :
    ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : R3 → ℝ) = φ := by
  rw [TestFunction.monoCLM_apply]
  simp [hV]

theorem integral_mono_test {V Ω : Opens R3} (hV : V ≤ Ω) (A : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : W1p (volume : Measure R3) Ω 2) (φ : 𝓓(V, ℝ)) :
    ∫ x in (Ω : Set R3), matrixBilinearForm (A x)
        (W1p.gradient (W1p.ofTestFunctionₗ (volume : Measure R3) Ω 2
          (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))) x) (W1p.gradient w x) =
      ∫ x in (V : Set R3), matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient (W1p.restrictL hV w) x) := by
  have h1 : ∫ x in (Ω : Set R3), matrixBilinearForm (A x)
        (W1p.gradient (W1p.ofTestFunctionₗ (volume : Measure R3) Ω 2
          (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))) x) (W1p.gradient w x) =
      ∫ x in (Ω : Set R3), matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient w x) := by
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
      (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx, coe_monoCLM hV]
  rw [h1, MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    Ω.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hV) (fun x hx => by
      simp [gradient_eq_zero_of_notMem φ hx.2])]
  refine integral_congr_ae ?_
  filter_upwards [W1p.gradient_restrictL_ae hV w] with x hx
  rw [hx]

theorem integral_mono_test_value {V Ω : Opens R3} (hV : V ≤ Ω) {U : Set R3}
    (hUΩ : U ⊆ (Ω : Set R3)) (h : R3 → ℝ) (φ : 𝓓(V, ℝ)) :
    ∫ x in U, h x * W1p.value (W1p.ofTestFunctionₗ (volume : Measure R3) Ω 2
          (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ))) x = ∫ x in U, h x * φ x := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hUΩ
    (testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2
      (TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)))] with x hx
  rw [W1p.value_ofTestFunctionₗ, hx, coe_monoCLM hV]

end OAI.AnisotropicCalderon.Regularity.RungeAux
