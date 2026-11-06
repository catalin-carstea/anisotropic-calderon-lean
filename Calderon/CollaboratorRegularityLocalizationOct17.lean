import Calderon.CollaboratorWholeSpaceH2Oct17
import TauCeti.Analysis.PDE.Regularity.Basic
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.TestFunctionLp
import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-! Localization of weak solutions on the unit ball by smooth multipliers, and interior `H²`
regularity for variable coefficients (helpers for task 05). -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge

section Generic

variable {ι : Type*} [Fintype ι]

lemma mbf_eq_sum (A : Matrix ι ι ℝ) (η ξ : EuclideanSpace ℝ ι) :
    matrixBilinearForm A η ξ = ∑ i, ∑ j, η i * (A i j * ξ j) := by
  simp [matrixBilinearForm_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]

/-- Sum of absolute values of the entries. -/
def entSum (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, |A i j|

lemma abs_mbf_le (A : Matrix ι ι ℝ) (η ξ : EuclideanSpace ℝ ι) :
    |matrixBilinearForm A η ξ| ≤ entSum A * ‖η‖ * ‖ξ‖ := by
  have hη : ∀ i, |η i| ≤ ‖η‖ := fun i => by simpa using PiLp.norm_apply_le η i
  have hξ : ∀ j, |ξ j| ≤ ‖ξ‖ := fun j => by simpa using PiLp.norm_apply_le ξ j
  rw [mbf_eq_sum]
  calc |∑ i, ∑ j, η i * (A i j * ξ j)| ≤ ∑ i, ∑ j, |η i * (A i j * ξ j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * ‖η‖ * ‖ξ‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        have := hη i; have := hξ j
        have : 0 ≤ |A i j| := abs_nonneg _
        calc |η i| * (|A i j| * |ξ j|) ≤ ‖η‖ * (|A i j| * ‖ξ‖) := by gcongr
          _ = _ := by ring
    _ = entSum A * ‖η‖ * ‖ξ‖ := by
        simp only [entSum, Finset.sum_mul]

omit [Fintype ι] in
lemma continuous_entry {X : Type*} [TopologicalSpace X] {a : X → Matrix ι ι ℝ}
    (ha : Continuous a) (i j : ι) : Continuous (fun x => a x i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp ha)

lemma continuous_entSum {X : Type*} [TopologicalSpace X] {a : X → Matrix ι ι ℝ}
    (ha : Continuous a) : Continuous (fun x => entSum (a x)) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_entry ha i j).abs

lemma continuous_mbf {X : Type*} [TopologicalSpace X] {a : X → Matrix ι ι ℝ}
    (ha : Continuous a) {g h : X → EuclideanSpace ℝ ι} (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun x => matrixBilinearForm (a x) (g x) (h x)) := by
  simp only [mbf_eq_sum]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((PiLp.continuous_apply 2 _ i).comp hg).mul
    ((continuous_entry ha i j).mul ((PiLp.continuous_apply 2 _ j).comp hh))

lemma aesm_mbf {μ : Measure (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : Continuous a) {g h : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    AEStronglyMeasurable (fun x => matrixBilinearForm (a x) (g x) (h x)) μ := by
  simp only [mbf_eq_sum]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  exact ((PiLp.continuous_apply 2 _ i).comp_aestronglyMeasurable hg).mul
    ((continuous_entry ha i j).aestronglyMeasurable.mul
      ((PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable hh))

lemma contDiff_matrix_entry {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) (i j : ι) : ContDiff ℝ ∞ (fun x => a x i j) := by
  have h1 : ContDiff ℝ ∞ (fun x => a x i) := contDiff_pi.1 ha i
  exact contDiff_pi.1 h1 j

lemma contDiff_coeff_gradient {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (η : EuclideanSpace ℝ ι) :
    ContDiff ℝ ∞ (fun y => matrixBilinearForm (a y) η (∇ ψ y)) := by
  simp only [mbf_eq_sum]
  have hg := hψ.gradient_right (m := ∞) (by simp)
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact contDiff_const.mul ((contDiff_matrix_entry ha i j).mul
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) j).contDiff.comp hg))

lemma gradient_mul_eq {f g : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ∇ (fun y => f y * g y) x = f x • ∇ g x + g x • ∇ f x := by
  simp only [gradient, fderiv_fun_mul hf hg, map_add, map_smul]

/-- The coefficient field applied to a gradient, `(a ∇ψ)ᵢ`, vanishes off `tsupport ψ`. -/
lemma tsupport_coeff_gradient_subset (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (ψ : EuclideanSpace ℝ ι → ℝ) (η : EuclideanSpace ℝ ι) :
    tsupport (fun y => matrixBilinearForm (a y) η (∇ ψ y)) ⊆ tsupport ψ :=
  closure_minimal (fun x hx => by_contra fun hxψ => hx (by
    simp [gradient_of_notMem_tsupport hxψ])) (isClosed_tsupport ψ)

/-- The divergence `div(a ∇ψ)` of the conormal field of `ψ` for a variable coefficient. -/
def divCoeffGradient (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, lineDeriv ℝ (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x
    (EuclideanSpace.basisFun ι ℝ i)

lemma divCoeffGradient_eq_zero_of_notMem_tsupport {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {x : EuclideanSpace ℝ ι} (hx : x ∉ tsupport ψ) :
    divCoeffGradient a ψ x = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have hxi : x ∉ tsupport (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun ι ℝ i)
      (∇ ψ y)) := fun h => hx (tsupport_coeff_gradient_subset a ψ _ h)
  have hd : DifferentiableAt ℝ
      (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x :=
    (contDiff_coeff_gradient ha hψ _).differentiable (by simp) x
  rw [hd.lineDeriv_eq_fderiv, fderiv_of_notMem_tsupport ℝ hxi]
  simp

lemma continuous_divCoeffGradient {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : Continuous (divCoeffGradient a ψ) := by
  refine continuous_finsetSum _ fun i _ => ?_
  have hh := contDiff_coeff_gradient ha hψ (EuclideanSpace.basisFun ι ℝ i)
  have heq : (fun x => lineDeriv ℝ (fun y => matrixBilinearForm (a y)
      (EuclideanSpace.basisFun ι ℝ i) (∇ ψ y)) x (EuclideanSpace.basisFun ι ℝ i)) =
      fun x => fderiv ℝ (fun y => matrixBilinearForm (a y) (EuclideanSpace.basisFun ι ℝ i)
        (∇ ψ y)) x (EuclideanSpace.basisFun ι ℝ i) :=
    funext fun x => ((hh.differentiable (by simp)) x).lineDeriv_eq_fderiv
  rw [heq]
  exact (hh.continuous_fderiv (by simp)).clm_apply continuous_const

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

/-- Integration by parts against the conormal field `a ∇ψ`, for a test function `φ` on `Ω`. -/
theorem setIntegral_value_mul_eq_neg_var {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) (u : W1p mu Omega 2)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (φ : 𝓓(Omega, ℝ)) :
    ∫ x in Omega, W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
        + φ x * divCoeffGradient a ψ x) ∂mu
      = -∫ x in Omega, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  set h : ι → EuclideanSpace ℝ ι → ℝ := fun i y => matrixBilinearForm (a y) (b i) (∇ ψ y)
  have hh : ∀ i, ContDiff ℝ ∞ (h i) := fun i => contDiff_coeff_gradient ha hψ (b i)
  have hsupp : ∀ i, Function.support (fun y => φ y * h i y) ⊆ tsupport φ := fun i x hx =>
    subset_tsupport _ (left_ne_zero_of_mul hx)
  let χ : ι → 𝓓(Omega, ℝ) := fun i =>
    ⟨fun y => φ y * h i y, φ.contDiff.mul (hh i), φ.hasCompactSupport.mono' (hsupp i),
      (closure_minimal (hsupp i) (isClosed_tsupport φ)).trans φ.tsupport_subset⟩
  have hχ : ∀ i, ((χ i : 𝓓(Omega, ℝ)) : EuclideanSpace ℝ ι → ℝ) = fun y => φ y * h i y :=
    fun _ => rfl
  have hloc := (W1p.hasWeakFDerivOn u).locallyIntegrableOn
  have key : ∀ i, ∫ x in Omega, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
        W1p.value u x ∂mu =
      -∫ x in Omega, (χ i : EuclideanSpace ℝ ι → ℝ) x • ⟪W1p.gradient u x, b i⟫_ℝ ∂mu := by
    intro i
    rw [setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul, setIntegral_smul_eq_integral_smul,
      ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn
        (b i)).integral_lineDeriv_smul_eq_neg_integral_smul (χ i)]
    simp [innerSL_apply_apply]
  have hderiv : ∀ i x, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i)
      = ⟪∇ φ x, b i⟫_ℝ * h i x + φ x * lineDeriv ℝ (h i) x (b i) := by
    intro i x
    have hφx : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable (by simp)) x
    have hhx : DifferentiableAt ℝ (h i) x := ((hh i).differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (fun y => φ y * h i y) x := hφx.mul hhx
    rw [hχ, hmul.lineDeriv_eq_fderiv, hhx.lineDeriv_eq_fderiv, fderiv_fun_mul hφx hhx,
      inner_gradient_left]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hint1 : ∀ i, Integrable (fun x => lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
      W1p.value u x) (mu.restrict Omega) :=
    fun i => (integrable_lineDeriv_smul_of_locallyIntegrableOn hloc (χ i) (b i)).restrict
  have hint2 : ∀ i, Integrable (fun x => (χ i : EuclideanSpace ℝ ι → ℝ) x •
      ⟪W1p.gradient u x, b i⟫_ℝ) (mu.restrict Omega) := fun i =>
    (integrable_smul_of_locallyIntegrableOn (w := fun x => ⟪W1p.gradient u x, b i⟫_ℝ)
      (by simpa [innerSL_apply_apply] using
        ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv)
      (χ i)).restrict
  calc ∫ x in Omega, W1p.value u x * (matrixBilinearForm (a x) (∇ φ x) (∇ ψ x)
        + φ x * divCoeffGradient a ψ x) ∂mu
      = ∫ x in Omega, ∑ i, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
          W1p.value u x ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hderiv, smul_eq_mul, divCoeffGradient]
        rw [← sum_inner_mul_matrixBilinearForm (A := a x)]
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add, add_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [h]
        ring
    _ = ∑ i, ∫ x in Omega, lineDeriv ℝ (χ i : EuclideanSpace ℝ ι → ℝ) x (b i) •
          W1p.value u x ∂mu := integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i, -∫ x in Omega, (χ i : EuclideanSpace ℝ ι → ℝ) x • ⟪W1p.gradient u x, b i⟫_ℝ ∂mu :=
        Finset.sum_congr rfl fun i _ => key i
    _ = -∫ x in Omega, ∑ i, (χ i : EuclideanSpace ℝ ι → ℝ) x • ⟪W1p.gradient u x, b i⟫_ℝ ∂mu := by
        rw [integral_finsetSum _ fun i _ => hint2 i, Finset.sum_neg_distrib]
    _ = -∫ x in Omega, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) ∂mu := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [← sum_inner_mul_matrixBilinearForm (A := a x), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hχ, h, smul_eq_mul]
        ring

/-- The forcing term of the localized equation (variable coefficient). -/
def locForcing (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ) (ψ : EuclideanSpace ℝ ι → ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) (x : EuclideanSpace ℝ ι) : ℝ :=
  ψ x * f x - matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)
    - matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) - W1p.value u x * divCoeffGradient a ψ x

lemma locForcing_eq_zero_of_notMem_tsupport {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) {x : EuclideanSpace ℝ ι}
    (hx : x ∉ tsupport ψ) : locForcing a ψ f u x = 0 := by
  simp [locForcing, image_eq_zero_of_notMem_tsupport hx, gradient_of_notMem_tsupport hx,
    divCoeffGradient_eq_zero_of_notMem_tsupport ha hψ hx]

theorem memLp_locForcing {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hΩb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) :
    MemLp (locForcing a ψ f u) 2 (mu.restrict Omega) := by
  have hK := hΩb.isCompact_closure
  have hΩm := Omega.isOpen.measurableSet
  have hac := ha.continuous
  have hE := continuous_entSum hac
  have hgψ := ContDiff.continuous_gradient hψ
  have hD := continuous_divCoeffGradient ha hψ
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hψ.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn
    (show Continuous fun x => entSum (a x) * ‖∇ ψ x‖ by fun_prop).continuousOn
  obtain ⟨C3, hC3⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ closure (Omega : Set (EuclideanSpace ℝ ι)) :=
    (ae_restrict_mem hΩm).mono fun x hx => subset_closure hx
  have h1 : MemLp (fun x => ψ x * f x) 2 (mu.restrict Omega) :=
    (Lp.memLp f).of_le_mul (c := C1)
      (hψ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (hmem.mono fun x hx => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hC1 x hx) (norm_nonneg _))
  have h2 : MemLp (fun x => matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)) 2
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := C2)
      (aesm_mbf hac (Lp.aestronglyMeasurable _) hgψ.aestronglyMeasurable)
      (hmem.mono fun x hx => by
        rw [Real.norm_eq_abs]
        refine (abs_mbf_le _ _ _).trans ?_
        have := (le_abs_self _).trans (hC2 x hx)
        calc _ = (entSum (a x) * ‖∇ ψ x‖) * ‖W1p.gradient u x‖ := by ring
          _ ≤ C2 * _ := mul_le_mul_of_nonneg_right this (norm_nonneg _))
  have h3 : MemLp (fun x => matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) 2
      (mu.restrict Omega) :=
    (Lp.memLp (W1p.gradient u)).of_le_mul (c := C2)
      (aesm_mbf hac hgψ.aestronglyMeasurable (Lp.aestronglyMeasurable _))
      (hmem.mono fun x hx => by
        rw [Real.norm_eq_abs]
        refine (abs_mbf_le _ _ _).trans ?_
        have := (le_abs_self _).trans (hC2 x hx)
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _))
  have h4 : MemLp (fun x => W1p.value u x * divCoeffGradient a ψ x) 2 (mu.restrict Omega) :=
    (Lp.memLp (W1p.value u)).of_le_mul (c := C3)
      ((Lp.aestronglyMeasurable _).mul hD.aestronglyMeasurable)
      (hmem.mono fun x hx => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hC3 x hx) (norm_nonneg _))
  exact ((h1.sub h2).sub h3).sub h4

/-- **The localized weak equation** against a test function on `Ω`. -/
theorem setIntegral_localized_eq {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x)
      (W1p.gradient u x) ∂mu = ∫ x in Omega, f x * φ x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (φ : 𝓓(Omega, ℝ)) :
    ∫ x in Omega, matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu
      = ∫ x in Omega, locForcing a ψ f u x * φ x ∂mu := by
  -- The test function `ψ φ`.
  have hsuppθ : Function.support (fun y => ψ y * φ y) ⊆ tsupport φ := fun x hx =>
    subset_tsupport _ (right_ne_zero_of_mul hx)
  let θ : 𝓓(Omega, ℝ) :=
    ⟨fun y => ψ y * φ y, hψ.mul φ.contDiff, φ.hasCompactSupport.mono' hsuppθ,
      (closure_minimal hsuppθ (isClosed_tsupport φ)).trans φ.tsupport_subset⟩
  have hθ : ((θ : 𝓓(Omega, ℝ)) : EuclideanSpace ℝ ι → ℝ) = fun y => ψ y * φ y := rfl
  have hE1 : ∫ x in Omega, matrixBilinearForm (a x) (ψ x • ∇ (φ : _ → ℝ) x + φ x • ∇ ψ x)
      (W1p.gradient u x) ∂mu = ∫ x in Omega, ψ x * f x * φ x ∂mu := by
    have h := hu θ
    rw [hθ] at h
    convert h using 1
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [gradient_mul_eq ((hψ.differentiable (by simp)) x)
        ((φ.contDiff.differentiable (by simp)) x)]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
  have hE2 := setIntegral_value_mul_eq_neg_var (mu := mu) ha u hψ φ
  have hac := ha.continuous
  have hE := continuous_entSum hac
  have hψ' := hψ.continuous
  have hφ' := φ.continuous
  have hgψ := ContDiff.continuous_gradient hψ
  have hgφ := continuous_gradient_testFunction φ
  have hD := continuous_divCoeffGradient ha hψ
  have hcs : ∀ K : EuclideanSpace ℝ ι → ℝ, (∀ x, φ x = 0 → ∇ (φ : _ → ℝ) x = 0 → K x = 0) →
      HasCompactSupport K := fun K hK =>
    φ.hasCompactSupport.mono' fun x hx => by_contra fun hxφ => hx (hK x
      (image_eq_zero_of_notMem_tsupport hxφ) (gradient_of_notMem_tsupport hxφ))
  have hu_m := Lp.aestronglyMeasurable (W1p.value u)
  have hgu_m := Lp.aestronglyMeasurable (W1p.gradient u)
  have hint : ∀ {F K g : EuclideanSpace ℝ ι → ℝ}, MemLp F 2 (mu.restrict Omega) → Continuous K →
      HasCompactSupport K → AEStronglyMeasurable g (mu.restrict Omega) →
      (∀ x, ‖g x‖ ≤ K x * F x) → Integrable g (mu.restrict Omega) :=
    fun hF hK hKc hg hle => ((hK.memLp_of_hasCompactSupport hKc (p := 2)).integrable_mul
      hF).mono' hg (Filter.Eventually.of_forall hle)
  have hbd : ∀ x (η ξ : EuclideanSpace ℝ ι),
      ‖matrixBilinearForm (a x) η ξ‖ ≤ entSum (a x) * ‖η‖ * ‖ξ‖ := fun x η ξ => by
    rw [Real.norm_eq_abs]; exact abs_mbf_le _ _ _
  have hT1 : Integrable (fun x => matrixBilinearForm (a x)
      (ψ x • ∇ (φ : _ → ℝ) x + φ x • ∇ ψ x) (W1p.gradient u x)) (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (K := fun x => entSum (a x) * ‖ψ x • ∇ (φ : _ → ℝ) x + φ x • ∇ ψ x‖) (by fun_prop)
      (hcs _ fun x h1 h2 => by simp [h1, h2])
      (aesm_mbf hac (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m)
      (fun x => hbd _ _ _)
  have hT2 : Integrable (fun x => φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (K := fun x => ‖φ x‖ * (entSum (a x) * ‖∇ ψ x‖)) (by fun_prop)
      (hcs _ fun x h1 _ => by simp [h1])
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aesm_mbf hac (Continuous.aestronglyMeasurable (by fun_prop)) hgu_m))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact hbd _ _ _)
  have hQ : Integrable (fun x => φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.gradient u)).norm
      (K := fun x => ‖φ x‖ * (entSum (a x) * ‖∇ ψ x‖)) (by fun_prop)
      (hcs _ fun x h1 _ => by simp [h1])
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aesm_mbf hac hgu_m (Continuous.aestronglyMeasurable (by fun_prop))))
      (fun x => by
        rw [norm_mul, mul_assoc]
        gcongr
        exact (hbd _ _ _).trans_eq (by ring))
  have hT3 : Integrable (fun x => W1p.value u x * (matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x)
      (∇ ψ x) + φ x * divCoeffGradient a ψ x)) (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.value u)).norm
      (K := fun x => ‖matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x) (∇ ψ x)
        + φ x * divCoeffGradient a ψ x‖)
      (continuous_norm.comp ((continuous_mbf hac hgφ hgψ).add (hφ'.mul hD)))
      (hcs _ fun x h1 h2 => by simp [h1, h2])
      (hu_m.mul (Continuous.aestronglyMeasurable
        ((continuous_mbf hac hgφ hgψ).add (hφ'.mul hD))))
      (fun x => by rw [norm_mul, mul_comm])
  have hT4 : Integrable (fun x => W1p.value u x * (φ x * divCoeffGradient a ψ x))
      (mu.restrict Omega) :=
    hint (Lp.memLp (W1p.value u)).norm
      (K := fun x => ‖φ x * divCoeffGradient a ψ x‖)
      (by fun_prop) (hcs _ fun x h1 _ => by simp [h1])
      (hu_m.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by rw [norm_mul, mul_comm])
  have hP : Integrable (fun x => ψ x * f x * φ x) (mu.restrict Omega) :=
    hint (Lp.memLp f).norm (K := fun x => ‖ψ x * φ x‖)
      (by fun_prop) (hcs _ fun x h1 _ => by simp [h1])
      (((Continuous.aestronglyMeasurable (by fun_prop)).mul (Lp.aestronglyMeasurable f)).mul
        (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => by
        simp only [norm_mul]
        exact le_of_eq (by ring))
  calc ∫ x in Omega, matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x)
        (ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) ∂mu
      = ∫ x in Omega, (matrixBilinearForm (a x) (ψ x • ∇ (φ : _ → ℝ) x + φ x • ∇ ψ x)
            (W1p.gradient u x)
          - φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)
          + W1p.value u x * (matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x) (∇ ψ x)
            + φ x * divCoeffGradient a ψ x)
          - W1p.value u x * (φ x * divCoeffGradient a ψ x)) ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        ring
    _ = (∫ x in Omega, ψ x * f x * φ x ∂mu)
          - ∫ x in Omega, φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x) ∂mu
          - ∫ x in Omega, φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x) ∂mu
          - ∫ x in Omega, W1p.value u x * (φ x * divCoeffGradient a ψ x) ∂mu := by
        rw [integral_sub ?_ hT4, integral_add ?_ hT3, integral_sub hT1 hT2, hE1, hE2]
        · ring
        · exact hT1.sub hT2
        · exact (hT1.sub hT2).add hT3
    _ = ∫ x in Omega, (ψ x * f x * φ x
          - φ x * matrixBilinearForm (a x) (W1p.gradient u x) (∇ ψ x)
          - φ x * matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)
          - W1p.value u x * (φ x * divCoeffGradient a ψ x)) ∂mu := by
        rw [integral_sub ?_ hT4, integral_sub ?_ hT2, integral_sub hP hQ]
        · exact hP.sub hQ
        · exact (hP.sub hQ).sub hT2
    _ = ∫ x in Omega, locForcing a ψ f u x * φ x ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [locForcing]
        ring

/-- **A cutoff of a local solution solves a whole-space equation.** -/
theorem exists_wholeSpace_solution {a ã : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ContDiff ℝ ∞ a) {Lam : ℝ} (hLam : 0 ≤ Lam) (hãc : Continuous ã)
    (hãb : ∀ x (η ξ : EuclideanSpace ℝ ι), |dotProduct η (Matrix.mulVec (ã x) ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hΩb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x)
      (W1p.gradient u x) ∂mu = ∫ x in Omega, f x * φ x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hagree : ∀ x ∈ tsupport ψ, ã x = a x) :
    ∃ w : W1p0 mu ⊤ 2, ∃ g : Lp ℝ 2
        (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))),
      IsWeakSolutionDirichlet ã 0 0 g w ∧
        ∀ᵐ x ∂mu, W1p.value (w : W1p mu ⊤ 2) x =
          (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => ψ y * W1p.value u y) x := by
  have hΩ := Omega.isOpen.measurableSet
  have hsub : (Omega : Set (EuclideanSpace ℝ ι)) ⊆
      ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) :=
    SetLike.coe_subset_coe.mpr le_top
  obtain ⟨M, hM, hψM, hgradM⟩ :=
    (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  have hw := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num)
    hψ hM hψM' hgradM' hψc hts u
  let w : W1p0 mu ⊤ 2 := W1p0.extendByZeroL le_top ⟨_, hw⟩
  have hwg := W1p.gradient_extendByZeroL_contDiffSMul_ae hψ hM hψM' hgradM' u hw
  have hG := memLp_locForcing ha hψ hΩb f u
  have hg : ∀ᵐ x ∂mu, extendByZeroLpₗᵢ ℝ mu hΩ hsub (hG.toLp (locForcing a ψ f u)) x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator (locForcing a ψ f u) x := by
    have h2 := (coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hΩ hsub
      (hG.toLp (locForcing a ψ f u))).filter_mono
        (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
    have h3 := (ae_restrict_iff' hΩ).1 hG.coeFn_toLp
    filter_upwards [h2, h3] with x hx2 hx3
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · rw [hx2, Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ, hx3 hxΩ]
    · rw [hx2, Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ]
  have hãm : AEStronglyMeasurable ã
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) := by
    have hb' : @Continuous (EuclideanSpace ℝ ι) (ι → ι → ℝ) _ _ ã := hãc
    exact hb'.aestronglyMeasurable
  have hcoeff : MemLp (fun x => energyIntegrand (ã x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι))) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hLam hãm
      aestronglyMeasurable_const aestronglyMeasurable_const (fun x _ => hãb x)
      (by simp) (by simp)
  -- A cutoff equal to one near `tsupport ψ`.
  obtain ⟨χ, hχ, -, hχ_one, hχc, hχts⟩ := hψc.isCompact.exists_contDiff_cutoff Omega.isOpen hts
  refine ⟨w, extendByZeroLpₗᵢ ℝ mu hΩ hsub (hG.toLp (locForcing a ψ f u)),
    (isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2
    (fun φ => ?_), W1p.value_extendByZeroL_contDiffSMul_ae hψ hM hψM' hgradM' u hw⟩
  have hsuppθ : Function.support (fun y => χ y * φ y) ⊆ tsupport χ := fun x hx =>
    subset_tsupport _ (left_ne_zero_of_mul hx)
  let θ : 𝓓(Omega, ℝ) :=
    ⟨fun y => χ y * φ y, hχ.mul φ.contDiff, hχc.mono' hsuppθ,
      (closure_minimal hsuppθ (isClosed_tsupport χ)).trans hχts⟩
  have hθ : ((θ : 𝓓(Omega, ℝ)) : EuclideanSpace ℝ ι → ℝ) = fun y => χ y * φ y := rfl
  have hχ1 : ∀ x ∈ tsupport ψ, (fun y => χ y * φ y) =ᶠ[nhds x] (φ : _ → ℝ) := by
    intro x hx
    filter_upwards [mem_interior_iff_mem_nhds.1 (hχ_one hx)] with y hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy, one_mul]
  have htop : mu.restrict ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) = mu := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hint_top : ∀ F : EuclideanSpace ℝ ι → ℝ,
      ∫ x in ((⊤ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)), F x ∂mu =
        ∫ x, F x ∂mu := fun F => by rw [htop]
  have hφg := (gradientTestFunctionLp_apply_ae (mu := mu) 2 φ).filter_mono (ae_mono htop.ge)
  rw [energyFormH1_def]
  simp only [energyIntegrand_apply, jetField_apply, Pi.zero_apply, driftForm_apply,
    massForm_apply, add_zero, zero_mul, inner_zero_left]
  rw [hint_top, hint_top]
  calc ∫ x, matrixBilinearForm (ã x) (W1p.gradient (W1p.ofTestFunctionₗ mu ⊤ 2 φ) x)
          (W1p.gradient (w : W1p mu ⊤ 2) x) ∂mu
      = ∫ x, (Omega : Set (EuclideanSpace ℝ ι)).indicator (fun y => matrixBilinearForm (a y)
          (∇ (θ : _ → ℝ) y) (ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y)) x ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hφg, hwg] with x h1 h2
        rw [W1p.gradient_ofTestFunctionₗ, h1, h2]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ]
          by_cases hxψ : x ∈ tsupport ψ
          · rw [hagree x hxψ, hθ, (hχ1 x hxψ).gradient_eq]
          · simp [image_eq_zero_of_notMem_tsupport hxψ, gradient_of_notMem_tsupport hxψ]
        · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ, map_zero]
    _ = ∫ x in Omega, locForcing a ψ f u x * θ x ∂mu := by
        rw [integral_indicator hΩ]
        exact setIntegral_localized_eq ha hu hψ θ
    _ = ∫ x, extendByZeroLpₗᵢ ℝ mu hΩ hsub (hG.toLp (locForcing a ψ f u)) x * φ x ∂mu := by
        rw [← integral_indicator hΩ]
        refine integral_congr_ae ?_
        filter_upwards [hg] with x h
        rw [h]
        by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
        · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ, hθ]
          by_cases hxψ : x ∈ tsupport ψ
          · simp only
            rw [(hχ1 x hxψ).eq_of_nhds]
          · simp [locForcing_eq_zero_of_notMem_tsupport ha hψ f u hxψ]
        · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ, zero_mul]

end Generic
lemma isBounded_ballOpens : Bornology.IsBounded (ballOpens : Set R3) :=
  Metric.isBounded_ball

/-- **Localization.** If `u ∈ H¹(B)` solves `-div(a ∇u) = f` against test functions and `ψ` is
smooth, then `ψ u` solves `-div(a ∇(ψ u)) = F` against test functions, with
`F = ψ f - ⟨∇ψ, a ∇u⟩ - ⟨∇u, a ∇ψ⟩ - u div(a ∇ψ) ∈ L²(B)`. The gradient of `ψ u` is written out
as `ψ ∇u + u ∇ψ`. -/
theorem exists_localized_forcing {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {u : W1p (volume : Measure R3) ballOpens 2}
    (hu : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient u x) =
        ∫ x in (ballOpens : Set R3), f x * φ x)
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ∃ F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
      ∀ φ : 𝓓(ballOpens, ℝ),
        ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
            (ψ x • W1p.gradient u x + W1p.value u x • gradient ψ x) =
          ∫ x in (ballOpens : Set R3), F x * φ x := by
  have hG := memLp_locForcing (mu := (volume : Measure R3)) ha hψ isBounded_ballOpens f u
  refine ⟨hG.toLp _, fun φ => ?_⟩
  rw [setIntegral_localized_eq ha hu hψ φ]
  refine integral_congr_ae ?_
  filter_upwards [hG.coeFn_toLp] with x hx
  rw [hx]

/-- `exists_localized_forcing` with the forcing identified: `F = locForcing a ψ f u` a.e. -/
theorem exists_localized_forcing_eq {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {u : W1p (volume : Measure R3) ballOpens 2}
    (hu : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient u x) =
        ∫ x in (ballOpens : Set R3), f x * φ x)
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ∃ F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
      (⇑F =ᵐ[(volume : Measure R3).restrict ballOpens] locForcing a ψ f u) ∧
      ∀ φ : 𝓓(ballOpens, ℝ),
        ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
            (ψ x • W1p.gradient u x + W1p.value u x • gradient ψ x) =
          ∫ x in (ballOpens : Set R3), F x * φ x := by
  have hG := memLp_locForcing (mu := (volume : Measure R3)) ha hψ isBounded_ballOpens f u
  refine ⟨hG.toLp _, hG.coeFn_toLp, fun φ => ?_⟩
  rw [setIntegral_localized_eq ha hu hψ φ]
  refine integral_congr_ae ?_
  filter_upwards [hG.coeFn_toLp] with x hx
  rw [hx]

/-- **Interior `H²` regularity.** Let `u ∈ H¹(B)` solve `-div(a ∇u) = f` against test functions,
let `ψ` be smooth with `tsupport ψ ⊆ B_{7/8}`, and let `ã` be a globally uniformly elliptic,
Lipschitz coefficient agreeing with `a` on `B_{7/8}`. Then `ψ u ∈ H²(B)`. -/
theorem exists_interior_H2 {a ã : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {lam Lam : ℝ} {K : NNReal} (hell : UniformlyEllipticOn (Set.univ : Set R3) ã lam Lam)
    (hlip : ∀ i j, LipschitzWith K (fun x => ã x i j))
    (hagree : ∀ x ∈ Metric.ball (0 : R3) (7 / 8), ã x = a x)
    {f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    {u : W1p (volume : Measure R3) ballOpens 2}
    (hu : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient u x) =
        ∫ x in (ballOpens : Set R3), f x * φ x)
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Metric.ball (0 : R3) (7 / 8)) :
    ∃ U : Wkp (volume : Measure R3) ballOpens 2 2,
      W1p.value (Wkp.lowerOrder 1 U) =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => ψ x * W1p.value u x := by
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall (0 : R3) (7 / 8)).of_isClosed_subset (isClosed_tsupport ψ)
      (hψs.trans Metric.ball_subset_closedBall)
  have hts : tsupport ψ ⊆ (ballOpens : Set R3) :=
    hψs.trans (Metric.ball_subset_ball (by norm_num))
  have hãc : Continuous ã :=
    continuous_pi fun i => continuous_pi fun j => (hlip i j).continuous
  have hsol := exists_wholeSpace_solution (mu := (volume : Measure R3)) ha hell.upper_nonneg hãc
    (fun x η ξ => hell.upper_bound (Set.mem_univ x) η ξ) isBounded_ballOpens hu hψ hψc hts
    (fun x hx => hagree x (hψs hx))
  obtain ⟨w, g, hwg, hval⟩ := hsol
  obtain ⟨U, hU⟩ := wholeSpace_exists_lowerOrder_eq hell hlip hwg
  have hle : ballOpens ≤ (⊤ : Opens R3) := le_top
  refine ⟨Wkp.restrictL hle 2 U, ?_⟩
  rw [Wkp.lowerOrder_restrictL, ← Wkp.value_one]
  filter_upwards [Wkp.value_restrictL_ae hle 1 (Wkp.lowerOrder 1 U),
    ae_restrict_of_ae hval, ae_restrict_mem ballOpens.isOpen.measurableSet] with x h1 h2 h3
  rw [h1, Wkp.value_one, hU, h2, Set.indicator_of_mem h3]

end OAI.AnisotropicCalderon.Regularity
