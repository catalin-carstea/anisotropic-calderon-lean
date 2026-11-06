import Calderon.CollaboratorRegularityCoefficientsOct17
import Calderon.CollaboratorRotationRegularityOct17
import Calderon.CollaboratorTangentialToH2Oct17
import Calderon.CollaboratorRegularityLocalizationOct17
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Task 05, base case `s = 0`: weak solutions with `L²` forcing are in `H²(B)`.

`u = ζ u + (1 - ζ) u` with a cutoff `ζ` equal to one on `B_{3/4}`. The interior piece is handled by
the whole-space theorem (`exists_interior_H2`); the boundary piece by rotational difference
quotients (`exists_hasWeakFDerivOn_rotational`) and the algebra of
`exists_lowerOrder_eq_of_tangential`. -/

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge

section Generic

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- The `H¹₀` energy form as an explicit integral. -/
theorem energyFormH1L0_eq_integral
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (u v : W1p0 mu Omega 2) :
    energyFormH1L0 hcoeff u v = ∫ x in Omega,
      matrixBilinearForm (a x) (W1p.gradient (v : W1p mu Omega 2) x)
        (W1p.gradient (u : W1p mu Omega 2) x) ∂mu := by
  rw [energyFormH1L0_apply, energyFormH1_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [energyIntegrand_apply]

end Generic

theorem inner_gen (j k : Fin 3) (x g : R3) :
    ⟪Rotation.gen j k x, g⟫_ℝ = x j * g k - x k * g j := by
  simp [Rotation.gen, inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left]


/-! ### Integrals of the bilinear form against `H¹₀` -/

/-- The matrix acting on `R3`, as a continuous linear map. -/
@[inline, reducible]
def mv (A : Matrix (Fin 3) (Fin 3) ℝ) : R3 →L[ℝ] R3 := Matrix.toEuclideanCLM (𝕜 := ℝ) A

theorem mbf_eq_inner (A : Matrix (Fin 3) (Fin 3) ℝ) (η ξ : R3) :
    matrixBilinearForm A η ξ = ⟪η, mv A ξ⟫_ℝ := by
  rw [matrixBilinearForm_apply, Matrix.inner_toEuclideanCLM]

theorem continuous_mv {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A) :
    Continuous fun x => mv (A x) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp
    hA

theorem exists_norm_mv_le {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A) :
    ∃ C, ∀ x ∈ (ballOpens : Set R3), ‖mv (A x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : R3) 1).exists_bound_of_continuousOn
    (continuous_mv hA).continuousOn
  exact ⟨C, fun x hx => hC x (ball_subset_closedBall (by simpa [B] using hx))⟩

theorem memLp_mv {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A)
    (G : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    MemLp (fun x => mv (A x) (G x)) 2 ((volume : Measure R3).restrict ballOpens) := by
  obtain ⟨C, hC⟩ := exists_norm_mv_le hA
  refine MemLp.of_le_mul (c := C) (Lp.memLp G)
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := R3) (F := R3)).continuous.comp_aestronglyMeasurable
      ((continuous_mv hA).aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G))) ?_
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
  exact ((mv (A x)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _))

theorem integral_mbf_eq_inner {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A)
    (G : Lp R3 2 ((volume : Measure R3).restrict ballOpens))
    (g : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x) (g x) (G x) =
      ⟪g, (memLp_mv hA G).toLp _⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_mv hA G).coeFn_toLp] with x hx
  rw [hx, mbf_eq_inner]

theorem integral_mul_eq_inner (F f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    ∫ x in (ballOpens : Set R3), F x * f x = ⟪f, F⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- An equation tested against test functions holds against all of `H¹₀(B)`. -/
theorem eq_of_testFunction {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A)
    {G : Lp R3 2 ((volume : Measure R3).restrict ballOpens)}
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    (htest : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (G x) =
        ∫ x in (ballOpens : Set R3), F x * φ x)
    (φ : W1p (volume : Measure R3) ballOpens 2)
    (hφ : φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2) :
    ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x) (W1p.gradient φ x) (G x) =
      ∫ x in (ballOpens : Set R3), F x * W1p.value φ x := by
  have hclosed : IsClosed {φ : W1p (volume : Measure R3) ballOpens 2 |
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x) (W1p.gradient φ x) (G x) =
        ∫ x in (ballOpens : Set R3), F x * W1p.value φ x} := by
    simp only [integral_mbf_eq_inner hA, integral_mul_eq_inner]
    exact isClosed_eq (W1p.gradientL.continuous.inner continuous_const)
      (W1p.valueL.continuous.inner continuous_const)
  refine w1p0Submodule_subset_of_isClosed hclosed (fun ψ => ?_) hφ
  refine (integral_congr_ae ?_).trans ((htest ψ).trans (integral_congr_ae ?_))
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]
  · filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x hx
    rw [W1p.value_ofTestFunctionₗ, hx]

/-- Conversely, an equation against `H¹₀(B)` holds against test functions. -/
theorem testFunction_of_eq {A : R3 → Matrix (Fin 3) (Fin 3) ℝ}
    {G : Lp R3 2 ((volume : Measure R3).restrict ballOpens)}
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    (h : ∀ φ : W1p (volume : Measure R3) ballOpens 2,
      φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x) (W1p.gradient φ x) (G x) =
        ∫ x in (ballOpens : Set R3), F x * W1p.value φ x)
    (ψ : 𝓓(ballOpens, ℝ)) :
    ∫ x in (ballOpens : Set R3), matrixBilinearForm (A x) (gradient (ψ : R3 → ℝ) x) (G x) =
      ∫ x in (ballOpens : Set R3), F x * ψ x := by
  have := h _ (W1p.ofTestFunctionₗ_mem_w1p0Submodule ψ)
  refine (integral_congr_ae ?_).trans (this.trans (integral_congr_ae ?_))
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]
  · filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 ψ] with x hx
    rw [W1p.value_ofTestFunctionₗ, hx]


theorem integrable_mbf {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A)
    (G g : Lp R3 2 ((volume : Measure R3).restrict ballOpens)) :
    Integrable (fun x => matrixBilinearForm (A x) (g x) (G x))
      ((volume : Measure R3).restrict ballOpens) := by
  refine (L2.integrable_inner (𝕜 := ℝ) g ((memLp_mv hA G).toLp _)).congr ?_
  filter_upwards [(memLp_mv hA G).coeFn_toLp] with x hx
  rw [hx, mbf_eq_inner]

/-! ### The base case -/

/-- **`H²` regularity of weak solutions with `L²` forcing.** -/
theorem exists_H2 {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam Lam : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ a (closedBall 0 2))
    (hell : UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    {f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {u : W1p (volume : Measure R3) ballOpens 2}
    (hu0 : u ∈ w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hu : ∀ φ : W1p (volume : Measure R3) ballOpens 2,
      φ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (W1p.gradient φ x) (W1p.gradient u x) =
        ∫ x in (ballOpens : Set R3), f x * W1p.value φ x) :
    ∃ U : Wkp (volume : Measure R3) ballOpens 2 2, Wkp.lowerOrder 1 U = u := by
  obtain ⟨â, hâ, hâa, hâc⟩ := exists_smooth_extension hsmooth
  have hlam : 0 < lam := hell.1
  have hB : ∀ x ∈ (ballOpens : Set R3), â x = a x := fun x hx => hâa x (by
    have : ‖x‖ < 1 := by simpa [B] using hx
    simp only [mem_closedBall, dist_zero_right]; linarith)
  have hmeas : MeasurableSet (ballOpens : Set R3) := ballOpens.isOpen.measurableSet
  -- the equation with the smooth coefficient `â`, against test functions
  have huâ : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (â x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient u x) =
        ∫ x in (ballOpens : Set R3), f x * φ x := by
    intro φ
    rw [← testFunction_of_eq hu φ]
    exact setIntegral_congr_fun hmeas fun x hx => by rw [hB x hx]
  -- ellipticity of `â` on the ball
  have hellâ : ∀ x ∈ (ballOpens : Set R3), ∀ ξ : R3,
      lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (â x) ξ ξ := by
    intro x hx ξ
    have := (hell.2.2 hx).1 ξ
    rwa [Matrix.toQuadraticForm'_apply, ← hB x hx, ← matrixBilinearForm_apply] at this
  -- the cutoff
  set ζ := bump (3 / 4) (13 / 16) (by norm_num) (by norm_num) with hζdef
  have hζs : tsupport ζ ⊆ ball (0 : R3) (7 / 8) := by
    rw [ζ.tsupport_eq]
    exact closedBall_subset_ball (by simp [ζ]; norm_num)
  have hζB : tsupport ζ ⊆ (ballOpens : Set R3) := fun x hx => by
    have := hζs hx
    simp only [coe_ballOpens, B, mem_ball] at this ⊢; linarith
  -- interior piece
  obtain ⟨K₂, hK₂⟩ := exists_lipschitz_ellExt hâ lam
  obtain ⟨Uint, hUint⟩ := exists_interior_H2 (a := â) (ã := ellExt â lam) hâ
    (uniformlyEllipticOn_ellExt hell hâa) hK₂ (fun x hx => ellExt_eq hx) huâ ζ.contDiff hζs
  -- boundary piece
  obtain ⟨M, hM, hζM, hgM⟩ :=
    ((ζ.contDiff (n := ⊤)).of_le (by simp)).exists_abs_le_and_norm_gradient_le ζ.hasCompactSupport
  set wζ := W1p.contDiffSMul ζ ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) u with hwζ
  have hwζ0 : wζ ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) ζ.contDiff hM
      (fun x _ => hζM x) (fun x _ => hgM x) ζ.hasCompactSupport hζB u
  set v := u - wζ with hvdef
  have hv0 : v ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    (w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.sub_mem hu0 hwζ0
  obtain ⟨Fζ, hFζ⟩ := exists_localized_forcing hâ huâ (ζ.contDiff (n := ⊤))
  have hgv : ⇑(W1p.gradient v) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => W1p.gradient u x - (ζ x • W1p.gradient u x + W1p.value u x • gradient ζ x) := by
    have : W1p.gradient v = W1p.gradient u - W1p.gradient wζ := by
      simp only [hvdef, ← W1p.gradientL_apply, map_sub]
    rw [this]
    filter_upwards [Lp.coeFn_sub (W1p.gradient u) (W1p.gradient wζ),
      W1p.gradient_contDiffSMul_ae ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) u]
      with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  have hvtest : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (â x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient v x) =
        ∫ x in (ballOpens : Set R3), (f - Fζ) x * φ x := by
    intro φ
    have hgφ := gradientTestFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ
    have hφ := testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ
    have e1 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (â x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient v x) =
        (∫ x in (ballOpens : Set R3), matrixBilinearForm (â x)
          (gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ x) (W1p.gradient u x)) -
        ∫ x in (ballOpens : Set R3), matrixBilinearForm (â x) (gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ x)
          (W1p.gradient wζ x) := by
      refine (integral_congr_ae ?_).trans (integral_sub
        (integrable_mbf hâ.continuous (W1p.gradient u) (gradientTestFunctionLp 2 φ))
        (integrable_mbf hâ.continuous (W1p.gradient wζ) (gradientTestFunctionLp 2 φ)))
      filter_upwards [hgφ, hgv, W1p.gradient_contDiffSMul_ae ζ.contDiff hM (fun x _ => hζM x)
        (fun x _ => hgM x) u] with x h1 h2 h3
      rw [h1, h2, ← h3, map_sub]
    have e2 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (â x)
        (gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ x) (W1p.gradient u x) =
        ∫ x in (ballOpens : Set R3), f x * φ x := by
      rw [← huâ φ]
      refine integral_congr_ae ?_
      filter_upwards [hgφ] with x h1
      rw [h1]
    have e3 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (â x)
        (gradientTestFunctionLp (mu := (volume : Measure R3)) 2 φ x) (W1p.gradient wζ x) =
        ∫ x in (ballOpens : Set R3), Fζ x * φ x := by
      rw [← hFζ φ]
      refine integral_congr_ae ?_
      filter_upwards [hgφ, W1p.gradient_contDiffSMul_ae ζ.contDiff hM (fun x _ => hζM x)
        (fun x _ => hgM x) u] with x h1 h2
      rw [h1, h2]
    have e4 : ∫ x in (ballOpens : Set R3), (f - Fζ) x * φ x =
        (∫ x in (ballOpens : Set R3), f x * φ x) - ∫ x in (ballOpens : Set R3), Fζ x * φ x := by
      have hi : ∀ F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
          Integrable (fun x => F x * φ x) ((volume : Measure R3).restrict ballOpens) := by
        intro F
        refine (L2.integrable_inner (𝕜 := ℝ) F (testFunctionLp (mu := (volume : Measure R3)) 2 φ)).congr ?_
        filter_upwards [hφ] with x hx
        rw [hx]
        simp [mul_comm]
      refine (integral_congr_ae ?_).trans (integral_sub (hi f) (hi Fζ))
      filter_upwards [Lp.coeFn_sub f Fζ] with x hx
      rw [hx, Pi.sub_apply, sub_mul]
    rw [e1, e2, e3, e4]
  have hvH := eq_of_testFunction hâ.continuous hvtest
  obtain ⟨K, hK⟩ := exists_lipschitz_entries hâ hâc
  have hz : ∀ j k : Fin 3, j ≠ k → ∃ G : Lp R3 2 ((volume : Measure R3).restrict ballOpens),
      HasWeakFDerivOn volume ballOpens
        (fun x => x j * W1p.gradient v x k - x k * W1p.gradient v x j)
        (fun x => innerSL ℝ (G x)) := by
    intro j k hjk
    obtain ⟨G, hG⟩ := Rotation.exists_hasWeakFDerivOn_rotational hlam hellâ hK hv0 hvH j k hjk
    refine ⟨G, ?_⟩
    simpa only [inner_gen] using hG
  have hval0 : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens,
      ‖x‖ < 3 / 4 → W1p.value v x = 0 := by
    have : W1p.value v = W1p.value u - W1p.value wζ := by
      simp only [hvdef, ← W1p.valueL_apply, map_sub]
    rw [this]
    filter_upwards [Lp.coeFn_sub (W1p.value u) (W1p.value wζ),
      W1p.value_contDiffSMul_ae ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) u]
      with x h1 h2 hx
    rw [h1, Pi.sub_apply, h2, ζ.one_of_mem_closedBall (by simp [ζ]; linarith), one_smul,
      sub_self]
  obtain ⟨Ubd, hUbd⟩ := exists_lowerOrder_eq_of_tangential hâ hlam hellâ v hval0 hz hvtest
  refine ⟨Uint + Ubd, ?_⟩
  have hlo : Wkp.lowerOrder 1 (Uint + Ubd) = Wkp.lowerOrder 1 Uint + Wkp.lowerOrder 1 Ubd :=
    map_add (Wkp.lowerOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1)
      Uint Ubd
  apply Wkp.ext 1
  rw [hlo, Wkp.value_add, hUbd, Wkp.value_one, Wkp.value_one v, Wkp.value_one u]
  apply Lp.ext
  have hv : W1p.value v = W1p.value u - W1p.value wζ := by
    simp only [hvdef, ← W1p.valueL_apply, map_sub]
  rw [hv]
  filter_upwards [Lp.coeFn_add (W1p.value (Wkp.lowerOrder 1 Uint)) (W1p.value u - W1p.value wζ),
    Lp.coeFn_sub (W1p.value u) (W1p.value wζ), hUint,
    W1p.value_contDiffSMul_ae ζ.contDiff hM (fun x _ => hζM x) (fun x _ => hgM x) u]
    with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul]
  ring

end OAI.AnisotropicCalderon.Regularity
