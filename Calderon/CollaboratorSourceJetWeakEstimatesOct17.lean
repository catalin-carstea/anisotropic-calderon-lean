import Calderon.CollaboratorSourceResponseHelpersOct17
import Calderon.CollaboratorLocalJetsOct17
import Calderon.CollaboratorLocalSobolevRawTwoJetBoundOct17

/-! Finite actual-data proof cuts for the direct L² source-jet route. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise Distributions Gradient
namespace OAI.AnisotropicCalderon.ExteriorSource.Literature.JetsAsm
open EnergyBridge DirichletFamily MetricVolume TauCeti TauCeti.PDE Regularity
open _root_.OAI.AnisotropicCalderon.Affine

/-- A function smooth on `ball p ρ₀` defines an element of `W^{1,2}(ball p ρ₁)`, `ρ₁ < ρ₀`. -/
theorem exists_w1p_of_contDiffOn {w : R3 → ℝ} {p : R3} {ρ₀ ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (h : ρ₁ < ρ₀) (hw : ContDiffOn ℝ ∞ w (ball p ρ₀)) :
    ∃ v : W1p (volume : Measure R3) (ballO p ρ₁) 2,
      ⇑(W1p.value v) =ᵐ[(volume : Measure R3).restrict (ball p ρ₁)] w := by
  let χ : ContDiffBump p := ⟨ρ₁, (ρ₁ + ρ₀) / 2, hρ₁, by linarith⟩
  have hχts : tsupport (χ : R3 → ℝ) ⊆ ball p ρ₀ := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (by simp [χ]; linarith)
  have hψ : ContDiff ℝ ∞ (fun z => χ z * w z) := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ ball p ρ₀
    · exact χ.contDiff.contDiffAt.mul (hw.contDiffAt (isOpen_ball.mem_nhds hy))
    · have hy' : y ∉ tsupport (χ : R3 → ℝ) := fun h => hy (hχts h)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hy'] with z hz
      simp [image_eq_zero_of_notMem_tsupport hz]
  let T : 𝓓((⊤ : Opens R3), ℝ) :=
    ⟨fun z => χ z * w z, hψ, χ.hasCompactSupport.mul_right, fun _ _ => trivial⟩
  have hle : ballO p ρ₁ ≤ ⊤ := le_top
  refine ⟨W1p.restrictL hle (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 T), ?_⟩
  have h1 := W1p.value_restrictL_ae hle (W1p.ofTestFunctionₗ (volume : Measure R3) ⊤ 2 T)
  have h2 := ae_restrict_of_ae_restrict_of_subset (Set.subset_univ (ball p ρ₁))
    (testFunctionLp_apply_ae (mu := (volume : Measure R3)) (Omega := ⊤) 2 T)
  filter_upwards [h1, h2, ae_restrict_mem (isOpen_ball (x := p) (ε := ρ₁)).measurableSet]
    with x hx1 hx2 hx3
  rw [hx1, W1p.value_ofTestFunctionₗ, hx2]
  show χ x * w x = w x
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall hx3), one_mul]

theorem jet_sub {u v : R3 → ℝ} {x : R3} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    Jets.jet (fun y => u y - v y) x = Jets.jet u x - Jets.jet v x := by
  have e : (fun y => u y - v y) = u + (-1 : ℝ) • v := by
    funext y; simp [sub_eq_add_neg]
  have hv' : ContDiffAt ℝ 2 ((-1 : ℝ) • v) x := hv.const_smul (-1 : ℝ)
  rw [e, Jets.jet_add hu hv', Jets.jet_smul _ hv, neg_one_smul, ← sub_eq_add_neg]

end OAI.AnisotropicCalderon.ExteriorSource.Literature.JetsAsm

namespace OAI.AnisotropicCalderon.ExteriorSource.Literature
open EnergyBridge DirichletFamily MetricVolume TauCeti TauCeti.PDE Regularity
open _root_.OAI.AnisotropicCalderon.Affine

/-- Original L² norm from the squared integral of the SAME AE representative. -/
theorem norm_lt_of_ae_integral_sq_lt (V : Opens R3)
    (F : Lp ℝ 2 ((volume : Measure R3).restrict V)) (v : R3 → ℝ)
    (hFv : (F : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict V] v)
    {t : ℝ} (ht : 0 ≤ t)
    (hint : ∫ x in (V : Set R3), v x ^ 2 < t ^ 2) : ‖F‖ < t := by
  have hsq : ‖F‖ ^ 2 = ∫ x in (V : Set R3), v x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hFv] with x hx
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]
  exact lt_of_pow_lt_pow_left₀ 2 ht (hsq.trans_lt hint)

/-- Interior regularity and the actual raw two-jet bound on the SAME native data. -/
theorem exists_weak_solution_rawJet_bound (p : R3) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ < r₂)
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (hpos : ∀ x, (A x).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : W1p (volume : Measure R3) (ballO p r₂) 2,
      (∀ φ : 𝓓(ballO p r₂, ℝ), ∫ x in ball p r₂,
        matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient w x) = 0) →
      ∀ u : R3 → ℝ, ContDiffOn ℝ ∞ u (ball p r₁) →
      (⇑(W1p.value w) =ᵐ[(volume : Measure R3).restrict (ball p r₁)] u) →
      ‖((u p, (fderiv ℝ u p, fderiv ℝ (fderiv ℝ u) p)) : RadiusTwoRawTwoJet)‖ ≤
        C * ‖W1p.value w‖ := by
  obtain ⟨CI, hCI, hest⟩ := interior_estimate p hr₁ hr hA hpos 5
  obtain ⟨CJ, hCJ, hjet⟩ := localSobolevRawTwoJetBound p r₁ hr₁
  refine ⟨CJ * CI, mul_nonneg hCJ hCI, fun w hw u hu hae => ?_⟩
  obtain ⟨V, hV, hVn⟩ := hest w hw
  have hVu : ⇑(Wkp.value 5 V) =ᵐ[(volume : Measure R3).restrict (ball p r₁)] u :=
    hV.trans hae
  calc
    ‖((u p, (fderiv ℝ u p, fderiv ℝ (fderiv ℝ u) p)) : RadiusTwoRawTwoJet)‖
        ≤ CJ * ‖V‖ := hjet V u hu hVu
    _ ≤ CJ * (CI * ‖W1p.value w‖) := mul_le_mul_of_nonneg_left hVn hCJ
    _ = (CJ * CI) * ‖W1p.value w‖ := by ring

/-- The SAME actual source response is weakly homogeneous wherever this source is zero. -/
theorem radiusTwoSourceSolution_restrict_weak_zero_of_source_zero
    (g : MatrixField) (hg : IsAdmissibleMetric g) (V : Opens R3)
    (hV : V ≤ ballO 0 2) (f : 𝓓(fixedExteriorSourceOpens, ℝ))
    (hf0 : ∀ x ∈ (V : Set R3), (f : R3 → ℝ) x = 0) (φ : 𝓓(V, ℝ)) :
    ∫ x in (V : Set R3), matrixBilinearForm (principalCoefficient g x)
      (gradient (φ : R3 → ℝ) x)
      (W1p.gradient (W1p.restrictL hV (Kresp g hg f)) x) = 0 := by
  have h1 := RungeAux.integral_mono_test hV (principalCoefficient g) (Kresp g hg f) φ
  have h2 := radiusTwoSourceSolution_integral g hg ⟨(f : R3 → ℝ), f.contDiff⟩
    (W1p.ofTestFunctionₗ (volume : Measure R3) (ballO 0 2) 2
      (TestFunction.monoCLM ℝ φ : 𝓓(ballO 0 2, ℝ)))
    (W1p.ofTestFunctionₗ_mem_w1p0Submodule _)
  have h3 := RungeAux.integral_mono_test_value hV (U := ball (0 : R3) 2) subset_rfl
    (f : R3 → ℝ) φ
  erw [← h1]
  refine h2.trans (h3.trans ?_)
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ (V : Set R3)
  · simp [hf0 x hx]
  · simp [RungeAux.eq_zero_of_notMem φ hx]

end OAI.AnisotropicCalderon.ExteriorSource.Literature
