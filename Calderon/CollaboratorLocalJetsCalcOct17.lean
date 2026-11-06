import Calderon.CollaboratorUniqueContinuationDefinitionOct17
import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Calculus helpers for `LocalJets` (Lassas–Liimatainen–Salo, Prop. A.5): affine changes of
variables in `divCoeffGrad`, 2-jets, the quadratic polynomial with a prescribed 2-jet, and
derivative bounds for rescaled functions. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Metric Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.Jets

/-- Raw 2-jets `(value, first derivative, second derivative)`. -/
@[inline, reducible]
def J := ℝ × ((R3 →L[ℝ] ℝ) × (R3 →L[ℝ] (R3 →L[ℝ] ℝ)))

/-- The 2-jet of `u` at `x`. -/
def jet (u : R3 → ℝ) (x : R3) : J := (u x, fderiv ℝ u x, fderiv ℝ (fderiv ℝ u) x)

/-- Standard basis vector. -/
@[inline, reducible]
def ee (i : Fin 3) : R3 := EuclideanSpace.single i (1 : ℝ)

/-! ### Affine changes of variables -/

noncomputable def smulCLE {c : ℝ} (hc : c ≠ 0) : R3 ≃L[ℝ] R3 :=
  ContinuousLinearEquiv.equivOfInverse (c • ContinuousLinearMap.id ℝ R3)
    (c⁻¹ • ContinuousLinearMap.id ℝ R3) (fun x => by simp [smul_smul, hc]) (fun x => by simp [smul_smul, hc])

theorem smulCLE_apply {c : ℝ} (hc : c ≠ 0) (x : R3) : smulCLE hc x = c • x := rfl

theorem fderiv_comp_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : R3 → F)
    (p₀ : R3) {c : ℝ} (hc : c ≠ 0) (y : R3) :
    fderiv ℝ (fun z => f (p₀ + c • z)) y = c • fderiv ℝ f (p₀ + c • y) := by
  have h1 : (fun z => f (p₀ + c • z)) = (fun w => f (p₀ + w)) ∘ smulCLE hc := rfl
  rw [h1, ContinuousLinearEquiv.comp_right_fderiv, fderiv_comp_add_left]
  ext v
  simp [smulCLE_apply, map_smul]

theorem divCoeffGrad_comp_affine (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) (p₀ : R3)
    {c : ℝ} (hc : c ≠ 0) (y : R3) :
    divCoeffGrad (fun z => A (p₀ + c • z)) (fun z => u (p₀ + c • z)) y =
      c ^ 2 * divCoeffGrad A u (p₀ + c • y) := by
  have := invertibleOfNonzero hc
  unfold divCoeffGrad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (fun z : R3 => ∑ j : Fin 3, A (p₀ + c • z) i j *
      fderiv ℝ (fun z => u (p₀ + c • z)) z (EuclideanSpace.single j 1)) =
      fun z => (c • fun x : R3 => ∑ j : Fin 3, A x i j * fderiv ℝ u x (EuclideanSpace.single j 1))
        (p₀ + c • z) := by
    funext z
    simp only [fderiv_comp_affine u p₀ hc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      FunLike.coe_smul, Pi.smul_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, fderiv_comp_affine _ p₀ hc, fderiv_const_smul_field]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem jet_comp_affine (u : R3 → ℝ) (p₀ : R3) {c : ℝ} (hc : c ≠ 0) (y : R3) :
    jet (fun z => u (p₀ + c • z)) y =
      (u (p₀ + c • y), c • fderiv ℝ u (p₀ + c • y),
        c ^ 2 • fderiv ℝ (fderiv ℝ u) (p₀ + c • y)) := by
  have := invertibleOfNonzero hc
  have h : fderiv ℝ (fun z => u (p₀ + c • z)) = fun z => (c • fderiv ℝ u) (p₀ + c • z) := by
    funext z; rw [fderiv_comp_affine u p₀ hc]; rfl
  simp only [jet, h]
  have h2 : fderiv ℝ (c • fderiv ℝ u) (p₀ + c • y) = c • fderiv ℝ (fderiv ℝ u) (p₀ + c • y) :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ u) (R := ℝ) c) _
  rw [fderiv_comp_affine _ p₀ hc, h2]
  simp only [Pi.smul_apply, smul_smul, sq]

/-! ### `divCoeffGrad` through the 2-jet -/

theorem differentiableAt_entry {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {x : R3}
    (hA : DifferentiableAt ℝ A x) (i j : Fin 3) : DifferentiableAt ℝ (fun z => A z i j) x :=
  differentiableAt_pi.1 (differentiableAt_pi.1 hA i) j

theorem differentiableAt_fderiv_of_contDiffAt {u : R3 → ℝ} {x : R3} (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (fderiv ℝ u) x :=
  (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem fderiv_fderiv_apply {u : R3 → ℝ} {x : R3} (hu : ContDiffAt ℝ 2 u x) (v w : R3) :
    fderiv ℝ (fun z => fderiv ℝ u z v) x w = fderiv ℝ (fderiv ℝ u) x w v := by
  rw [fderiv_clm_apply (differentiableAt_fderiv_of_contDiffAt hu) (differentiableAt_const v)]
  simp

/-- The 2-jet expression of `div(A ∇u)(x)` (this is `jetFunctional A x (Du x) (D²u x)`). -/
theorem divCoeffGrad_eq_jet {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {u : R3 → ℝ} {x : R3}
    (hA : DifferentiableAt ℝ A x) (hu : ContDiffAt ℝ 2 u x) :
    divCoeffGrad A u x = ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun z : R3 => A z i j) x (EuclideanSpace.single i 1) *
        fderiv ℝ u x (EuclideanSpace.single j 1) +
      A x i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) := by
  unfold divCoeffGrad
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : ∀ j : Fin 3, DifferentiableAt ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) x :=
    fun j => (differentiableAt_fderiv_of_contDiffAt hu).clm_apply (differentiableAt_const _)
  rw [fderiv_fun_sum (A := fun j z => A z i j * fderiv ℝ u z (EuclideanSpace.single j 1))
    fun j _ => (differentiableAt_entry hA i j).mul (hd j)]
  simp only [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_mul (differentiableAt_entry hA i j) (hd j)]
  simp only [add_apply, smul_apply, smul_eq_mul,
    fderiv_fderiv_apply hu]
  ring

/-- Jets of a sum, near points where both summands are `C²`. -/
theorem jet_add {u v : R3 → ℝ} {x : R3} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    jet (u + v) x = jet u x + jet v x := by
  have h1 : fderiv ℝ (u + v) =ᶠ[nhds x] fderiv ℝ u + fderiv ℝ v := by
    filter_upwards [hu.eventually (by simp), hv.eventually (by simp)] with z hz1 hz2
    exact fderiv_add (hz1.differentiableAt (by norm_num)) (hz2.differentiableAt (by norm_num))
  simp only [jet, Prod.mk_add_mk, Pi.add_apply]
  rw [h1.fderiv_eq, fderiv_add (differentiableAt_fderiv_of_contDiffAt hu)
    (differentiableAt_fderiv_of_contDiffAt hv),
    fderiv_add (hu.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num))]

theorem jet_smul {u : R3 → ℝ} {x : R3} (c : ℝ) (hu : ContDiffAt ℝ 2 u x) :
    jet (c • u) x = c • jet u x := by
  have h1 : fderiv ℝ (c • u) = c • fderiv ℝ u := fderiv_const_smul_field (𝕜 := ℝ) (f := u) (R := ℝ) c
  have h2 : fderiv ℝ (c • fderiv ℝ u) = c • fderiv ℝ (fderiv ℝ u) :=
    fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ u) (R := ℝ) c
  simp only [jet, h1, h2, Prod.smul_mk, Pi.smul_apply]

theorem jet_zero (x : R3) : jet (0 : R3 → ℝ) x = 0 := by
  simp [jet]

/-- Symmetry of the second derivative. -/
theorem jet_symm {u : R3 → ℝ} {x : R3} (hu : ContDiffAt ℝ 2 u x) (v w : R3) :
    (jet u x).2.2 v w = (jet u x).2.2 w v :=
  (ContDiffAt.isSymmSndFDerivAt hu (by simp)) v w

theorem divCoeffGrad_add {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {u v : R3 → ℝ} {x : R3}
    (hA : DifferentiableAt ℝ A x) (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    divCoeffGrad A (u + v) x = divCoeffGrad A u x + divCoeffGrad A v x := by
  have h := jet_add hu hv
  simp only [jet, Prod.mk_add_mk, Prod.mk.injEq] at h
  rw [divCoeffGrad_eq_jet (u := u + v) hA (hu.add hv), divCoeffGrad_eq_jet hA hu, divCoeffGrad_eq_jet hA hv,
    h.2.1, h.2.2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [add_apply]
  ring

theorem divCoeffGrad_smul {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {u : R3 → ℝ} {x : R3} (c : ℝ)
    (hA : DifferentiableAt ℝ A x) (hu : ContDiffAt ℝ 2 u x) :
    divCoeffGrad A (c • u) x = c * divCoeffGrad A u x := by
  have h := jet_smul c hu
  simp only [jet, Prod.smul_mk, Prod.mk.injEq] at h
  rw [divCoeffGrad_eq_jet (u := c • u) hA (hu.const_smul c), divCoeffGrad_eq_jet hA hu, h.2.1, h.2.2,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_apply, smul_eq_mul]
  ring

/-! ### The quadratic polynomial with a prescribed jet -/

/-- `q(x) = a + ξ(x - p) + ½ H(x - p)(x - p)`. -/
def quad (p : R3) (c : J) : R3 → ℝ :=
  fun x => c.1 + c.2.1 (x - p) + (1 / 2 : ℝ) * c.2.2 (x - p) (x - p)

theorem hasFDerivAt_quad (p : R3) {c : J} (hH : ∀ v w, c.2.2 v w = c.2.2 w v) (x : R3) :
    HasFDerivAt (quad p c) (c.2.1 + c.2.2 (x - p)) x := by
  have h1 : HasFDerivAt (fun z : R3 => z - p) (ContinuousLinearMap.id ℝ R3) x :=
    (hasFDerivAt_id x).sub_const p
  have h2 : HasFDerivAt (fun z : R3 => c.2.2 (z - p)) c.2.2 x := by
    have := c.2.2.hasFDerivAt.comp x h1
    rwa [ContinuousLinearMap.comp_id] at this
  have h3 := h2.clm_apply h1
  have h4 : HasFDerivAt (fun z : R3 => c.2.1 (z - p)) c.2.1 x := by
    have := c.2.1.hasFDerivAt.comp x h1
    rwa [ContinuousLinearMap.comp_id] at this
  have h5 := ((h4.const_add c.1).add (h3.const_mul (1 / 2 : ℝ)))
  have e : quad p c = ((fun x => c.1 + c.2.1 (x - p)) + fun y => 1 / 2 * c.2.2 (y - p) (y - p)) :=
    rfl
  rw [e]
  refine h5.congr_fderiv ?_
  ext v
  simp
  rw [hH v x, hH v p]
  ring

theorem contDiff_quad (p : R3) (c : J) : ContDiff ℝ ∞ (quad p c) := by
  unfold quad
  fun_prop

theorem fderiv_quad (p : R3) {c : J} (hH : ∀ v w, c.2.2 v w = c.2.2 w v) (x : R3) :
    fderiv ℝ (quad p c) x = c.2.1 + c.2.2 (x - p) :=
  (hasFDerivAt_quad p hH x).fderiv

theorem fderiv_fderiv_quad (p : R3) {c : J} (hH : ∀ v w, c.2.2 v w = c.2.2 w v) (x : R3) :
    fderiv ℝ (fderiv ℝ (quad p c)) x = c.2.2 := by
  have : fderiv ℝ (quad p c) = fun z => c.2.1 + c.2.2 (z - p) := funext (fderiv_quad p hH)
  rw [this]
  have h1 : HasFDerivAt (fun z : R3 => z - p) (ContinuousLinearMap.id ℝ R3) x :=
    (hasFDerivAt_id x).sub_const p
  have h2 : HasFDerivAt (fun z : R3 => c.2.2 (z - p)) c.2.2 x := by
    have := c.2.2.hasFDerivAt.comp x h1
    rwa [ContinuousLinearMap.comp_id] at this
  exact (h2.const_add c.2.1).fderiv

theorem jet_quad (p : R3) {c : J} (hH : ∀ v w, c.2.2 v w = c.2.2 w v) : jet (quad p c) p = c := by
  simp [jet, fderiv_quad p hH, fderiv_fderiv_quad p hH, quad]

/-! ### The forcing functional `Γ` -/

/-- `Γ x c = div(A ∇ quad p c)(x)`, as a continuous linear functional of the jet `c`. -/
def Γ (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : R3) (x : R3) : J →L[ℝ] ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (fderiv ℝ (fun z : R3 => A z i j) x (ee i) •
        ((ContinuousLinearMap.apply ℝ ℝ (ee j)).comp
          ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ ℝ _)) +
        ∑ l : Fin 3, (x - p) l •
          ((ContinuousLinearMap.apply ℝ ℝ (ee j)).comp
            ((ContinuousLinearMap.apply ℝ (R3 →L[ℝ] ℝ) (ee l)).comp
              ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ ℝ _))))) +
      A x i j • ((ContinuousLinearMap.apply ℝ ℝ (ee j)).comp
            ((ContinuousLinearMap.apply ℝ (R3 →L[ℝ] ℝ) (ee i)).comp
              ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ ℝ _)))))

theorem contDiff_Γ {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (p : R3) :
    ContDiff ℝ ∞ (Γ A p) := by
  have he : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => A z i j) := fun i j =>
    (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 3 → ℝ) i).comp hA)
  have hd : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => fderiv ℝ (fun z => A z i j) x (ee i)) :=
    fun i j => ((he i j).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  unfold Γ
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  refine ((hd i j).smul (contDiff_const.add (ContDiff.sum fun l _ => ?_))).add ((he i j).smul contDiff_const)
  exact ((((EuclideanSpace.proj l : R3 →L[ℝ] ℝ)).contDiff).comp (contDiff_id.sub contDiff_const)).smul contDiff_const

theorem Γ_apply_self (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (p : R3) (c : J) :
    Γ A p p c = ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun z : R3 => A z i j) p (EuclideanSpace.single i 1) *
        c.2.1 (EuclideanSpace.single j 1) +
      A p i j * c.2.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  simp [Γ]

theorem sum_coord_smul (v : R3) : ∑ l : Fin 3, v l • ee l = v := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simpa [EuclideanSpace.basisFun_apply] using this

theorem divCoeffGrad_quad {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (p : R3)
    {c : J} (hH : ∀ v w, c.2.2 v w = c.2.2 w v) (x : R3) :
    divCoeffGrad A (quad p c) x = Γ A p x c := by
  rw [divCoeffGrad_eq_jet (hA.differentiable (by simp) x)
    ((contDiff_quad p c).contDiffAt.of_le (by simp)), fderiv_quad p hH, fderiv_fderiv_quad p hH]
  have hx : ∀ j, c.2.2 (x - p) (EuclideanSpace.single j 1) =
      ∑ l : Fin 3, (x - p) l * c.2.2 (ee l) (ee j) := by
    intro j
    conv_lhs => rw [← sum_coord_smul (x - p)]
    simp [map_sum]
  simp only [add_apply, hx]
  simp [Γ, mul_add, Finset.mul_sum]

/-! ### Derivative bounds -/

/-- Uniform bounds of the derivatives of a smooth function on a compact set. -/
theorem exists_bound_iteratedFDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : R3 → F} (hG : ContDiff ℝ ∞ G) {K : Set R3} (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ j G x‖ ≤ C := by
  have h : ∀ j : ℕ, ∃ C, ∀ x ∈ K, ‖iteratedFDeriv ℝ j G x‖ ≤ C := fun j =>
    hK.exists_bound_of_continuousOn
      (hG.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using h
  refine ⟨∑ j ∈ Finset.range (n + 1), |C j|, Finset.sum_nonneg fun j _ => abs_nonneg _,
    fun j hj x hx => (hC j x hx).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

/-- Derivative bounds for `y ↦ G (p + c • y)` from `G` evaluated at a fixed vector. -/
theorem norm_iteratedFDeriv_Γ_le {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (p : R3) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : J), ∀ j ≤ 5, ∀ x ∈ closedBall p 2,
      ‖iteratedFDeriv ℝ j (fun x => Γ A p x c) x‖ ≤ K * ‖c‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_iteratedFDeriv (contDiff_Γ hA p) (isCompact_closedBall p 2) 5
  refine ⟨K, hK0, fun c j hj x hx => ?_⟩
  have e : (fun x => Γ A p x c) = (ContinuousLinearMap.apply ℝ ℝ c) ∘ Γ A p := rfl
  rw [e]
  refine ((ContinuousLinearMap.apply ℝ ℝ c).norm_iteratedFDeriv_comp_left
    (contDiff_Γ hA p).contDiffAt (by exact_mod_cast le_top)).trans ?_
  have hn : ‖ContinuousLinearMap.apply ℝ ℝ c‖ ≤ ‖c‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => by
      rw [ContinuousLinearMap.apply_apply, mul_comm]; exact f.le_opNorm c
  calc ‖ContinuousLinearMap.apply ℝ ℝ c‖ * ‖iteratedFDeriv ℝ j (Γ A p) x‖
      ≤ ‖c‖ * K := mul_le_mul hn (hK j hj x hx) (norm_nonneg _) (norm_nonneg _)
    _ = K * ‖c‖ := mul_comm _ _

/-- Derivative bounds after rescaling `y ↦ G (p + ε y) - G p` on `closedBall 0 2`. -/
theorem norm_iteratedFDeriv_rescale_le {G : R3 → ℝ} (hG : ContDiff ℝ ∞ G) {p : R3} {n : ℕ}
    {K : ℝ} (hK : ∀ j ≤ n, ∀ x ∈ closedBall p 2, ‖iteratedFDeriv ℝ j G x‖ ≤ K) (hn : 1 ≤ n)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ j ≤ n, ∀ y ∈ closedBall (0 : R3) 2,
      ‖iteratedFDeriv ℝ j (fun y => G (p + ε • y) - G p) y‖ ≤ 2 * K * ε := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (Nat.zero_le _) p (mem_closedBall_self (by norm_num)))
  intro j hj y hy
  have hy' : ‖y‖ ≤ 2 := by simpa using hy
  have hmem : p + ε • y ∈ closedBall p 2 := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε]
    nlinarith [norm_nonneg y]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [norm_iteratedFDeriv_zero]
    have hmv := (convex_closedBall p 2).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => (hG.differentiable (by simp)) x)
      (fun x hx => by rw [← norm_iteratedFDeriv_one]; exact hK 1 hn x hx)
      (mem_closedBall_self (by norm_num)) hmem
    refine hmv.trans ?_
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith [mul_le_mul_of_nonneg_left hy' (mul_nonneg hK0 hε.le)]
  · have hsub : iteratedFDeriv ℝ j (fun y => G (p + ε • y) - G p) y =
        iteratedFDeriv ℝ j (fun y => G (p + ε • y)) y := by
      have h1 : ContDiff ℝ ∞ (fun y : R3 => G (p + ε • y)) :=
        hG.comp (contDiff_const.add (contDiff_const_smul ε))
      show iteratedFDeriv ℝ j ((fun y => G (p + ε • y)) - fun _ => G p) y = _
      rw [iteratedFDeriv_sub_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top))
        contDiffAt_const, iteratedFDeriv_const_of_ne (by omega)]
      simp
    rw [hsub]
    have h2 : ContDiff ℝ j (fun w : R3 => G (p + w)) :=
      (hG.comp (contDiff_const.add contDiff_id)).of_le (by exact_mod_cast le_top)
    rw [iteratedFDeriv_comp_const_smul ε h2]
    show ‖ε ^ j • iteratedFDeriv ℝ j (fun w => G (p + w)) (ε • y)‖ ≤ _
    rw [iteratedFDeriv_comp_add_left, norm_smul,
      norm_pow, Real.norm_eq_abs, abs_of_pos hε]
    have hpow : ε ^ j ≤ ε := by
      calc ε ^ j ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 hjpos
        _ = ε := pow_one ε
    have hb := hK j hj _ hmem
    calc ε ^ j * ‖iteratedFDeriv ℝ j G (p + ε • y)‖ ≤ ε * K :=
          mul_le_mul hpow hb (norm_nonneg _) hε.le
      _ ≤ 2 * K * ε := by nlinarith

/-! ### Uniform ellipticity from positive definiteness -/

open Matrix in
theorem exists_uniformlyEllipticOn {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : Continuous A)
    (hpos : ∀ x, (A x).PosDef) {K : Set R3} (hK : IsCompact K) :
    ∃ lam Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn K A lam Lam := by
  -- upper bound
  have hcont : Continuous fun x => ‖TauCeti.PDE.matrixBilinearForm (A x)‖ :=
    (continuous_norm (E := R3 →L[ℝ] R3 →L[ℝ] ℝ)).comp
      (TauCeti.PDE.continuous_matrixBilinearForm.comp hA)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hcont.continuousOn
  -- lower bound
  let Q : R3 × R3 → ℝ := fun z => z.2 ⬝ᵥ (A z.1 *ᵥ z.2)
  have hvec : Continuous fun z : R3 × R3 => (z.2 : Fin 3 → ℝ) :=
    continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp continuous_snd
  have hQ : Continuous Q :=
    hvec.dotProduct ((hA.comp continuous_fst).matrix_mulVec hvec)
  have hKs := hK.prod (isCompact_sphere (0 : R3) 1)
  obtain ⟨lam, hlam, hlamQ⟩ := hKs.exists_forall_le' hQ.continuousOn (a := (0 : ℝ)) (by
    intro z hz
    have hnorm : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    have hv : (z.2 : Fin 3 → ℝ) ≠ 0 := by
      intro hv
      have he : z.2 = 0 := by ext i; exact congrFun hv i
      simp [he] at hnorm
    simpa [Q] using (hpos z.1).dotProduct_mulVec_pos hv)
  refine ⟨lam, max M lam, hlam, le_max_right _ _, ?_⟩
  intro x hx
  refine ⟨fun ξ => ?_, fun η ξ => ?_⟩
  · by_cases hξ : ξ = 0
    · simp [hξ]
    have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    have hs : (‖ξ‖⁻¹ • ξ : R3) ∈ Metric.sphere 0 1 := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hb := hlamQ (x, ‖ξ‖⁻¹ • ξ) ⟨hx, hs⟩
    have hscaled : (A x).toQuadraticForm' (‖ξ‖⁻¹ • ξ) =
        ‖ξ‖⁻¹ ^ 2 * (A x).toQuadraticForm' ξ := by
      simpa [pow_two, smul_eq_mul] using
        (A x).toQuadraticForm'.map_smul ‖ξ‖⁻¹ (ξ : Fin 3 → ℝ)
    have hb' : lam ≤ ‖ξ‖⁻¹ ^ 2 * (A x).toQuadraticForm' ξ := by
      rw [← hscaled]
      simpa only [Q, Matrix.toQuadraticForm'_apply, WithLp.ofLp_smul] using hb
    have hm := mul_le_mul_of_nonneg_left hb' (sq_nonneg ‖ξ‖)
    have he : ‖ξ‖ ^ 2 * (‖ξ‖⁻¹ ^ 2 * (A x).toQuadraticForm' ξ) = (A x).toQuadraticForm' ξ := by
      field_simp [hn]
    rw [he] at hm
    simpa only [mul_comm] using hm
  · have hb : ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ max M lam :=
      (hM (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)
    calc
      |η ⬝ᵥ (A x *ᵥ ξ)| = ‖TauCeti.PDE.matrixBilinearForm (A x) η ξ‖ := by
        rw [TauCeti.PDE.matrixBilinearForm_apply, Real.norm_eq_abs]
      _ ≤ ‖TauCeti.PDE.matrixBilinearForm (A x)‖ * ‖η‖ * ‖ξ‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ max M lam * ‖η‖ * ‖ξ‖ := by gcongr

end OAI.AnisotropicCalderon.Regularity.Jets
