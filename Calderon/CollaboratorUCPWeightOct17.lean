import Calderon.CollaboratorUCPIdentityOct17

/-! # The weight `φ = exp (λ ψ)`: explicit coefficients of the Carleman integrand -/

noncomputable section
open MeasureTheory
open scoped ContDiff
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace OAI.AnisotropicCalderon

section
variable (a : Fin 3 → Fin 3 → R3 → ℝ) (ψ : R3 → ℝ) (lam : ℝ)

/-- `b = a ∇ψ`. -/
def bv (j : Fin 3) (z : R3) : ℝ := ∑ k, a j k z * pd k ψ z
/-- `N = |∇ψ|²_a`. -/
def Nf (z : R3) : ℝ := ∑ j, bv a ψ j z * pd j ψ z
/-- `φ = exp (λ ψ)`. -/
def phi (z : R3) : ℝ := Real.exp (lam * ψ z)
/-- `τ`-free part of `X = a ∇(τ φ)`. -/
def Xs (j : Fin 3) (z : R3) : ℝ := lam * phi ψ lam z * bv a ψ j z
/-- `τ`-free part of `θ`. -/
def θs (z : R3) : ℝ := lam ^ 2 * phi ψ lam z
/-- Error in the gradient coefficient. -/
def E1 (x : R3) (ξ : Fin 3 → ℝ) : ℝ :=
  4 * ∑ i, ∑ j, ∑ l, a i l x * ξ l * pd i (bv a ψ j) x * ξ j -
    2 * ∑ j, bv a ψ j x * ∑ i, ∑ k, pd j (a i k) x * ξ i * ξ k
/-- `τ`-linear part of the zero-order coefficient. -/
def Rf (κ : ℝ) (x : R3) : ℝ := Lop a (divV (Xs a ψ lam)) x + κ * Lop a (θs ψ lam) x
/-- Lower-order part of the `τ³` coefficient. -/
def Pf (x : R3) : ℝ := ∑ j, bv a ψ j x * pd j (Nf a ψ) x

theorem bv_apply (j : Fin 3) (z : R3) : bv a ψ j z = ∑ k, a j k z * pd k ψ z := rfl
theorem Nf_apply (z : R3) : Nf a ψ z = ∑ j, bv a ψ j z * pd j ψ z := rfl
end

section
variable {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
include ha hψ

@[fun_prop] theorem contDiff_bv (j : Fin 3) : ContDiff ℝ ∞ (bv a ψ j) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold bv; fun_prop

@[fun_prop] theorem contDiff_Nf : ContDiff ℝ ∞ (Nf a ψ) := by
  have := contDiff_bv ha hψ
  unfold Nf; fun_prop

omit ha in
@[fun_prop] theorem contDiff_phi (lam : ℝ) : ContDiff ℝ ∞ (phi ψ lam) := by
  unfold phi; fun_prop

omit ha in
theorem pd_phi (lam : ℝ) (i : Fin 3) (x : R3) :
    pd i (phi ψ lam) x = lam * phi ψ lam x * pd i ψ x := by
  have h : phi ψ lam = fun z => Real.exp (lam * ψ z) := rfl
  rw [h, pd_exp (by fun_prop), pd_const_mul _ hψ]
  simp only [phi]; ring

end

theorem pd_sq {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) (x : R3) :
    pd i (fun y => f y ^ 2) x = 2 * f x * pd i f x := by
  simp only [sq]; rw [pd_mul hf hf]; ring

theorem divV_smul {Y : Fin 3 → R3 → ℝ} (hY : ∀ j, ContDiff ℝ ∞ (Y j)) (τ : ℝ) :
    divV (fun j z => τ * Y j z) = fun z => τ * divV Y z := by
  funext z
  simp only [divV, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => pd_const_mul τ (hY j) z

theorem Lop_smul {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (τ : ℝ) (x : R3) :
    Lop a (fun z => τ * f z) x = τ * Lop a f x := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  simp only [Lop]
  simp (disch := fun_prop) only [pd_const_mul, pd_sum, pd_mul]
  simp only [Fin.sum_univ_three]; ring

section spec
variable {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (lam τ κ : ℝ)
include ha hψ

theorem X_eq : (fun j y => ∑ k, a j k y * pd k (fun z => τ * phi ψ lam z) y) =
    fun j z => τ * Xs a ψ lam j z := by
  funext j y
  simp (disch := fun_prop) only [pd_const_mul, pd_phi hψ]
  simp only [Xs, bv_apply, Fin.sum_univ_three]; ring

theorem q_eq : (fun y => ∑ i, ∑ k, a i k y * pd i (fun z => τ * phi ψ lam z) y *
      pd k (fun z => τ * phi ψ lam z) y) =
    fun z => τ ^ 2 * (lam ^ 2 * phi ψ lam z ^ 2 * Nf a ψ z) := by
  funext y
  simp (disch := fun_prop) only [pd_const_mul, pd_phi hψ]
  simp only [Nf_apply, bv_apply, Fin.sum_univ_three]; ring

include hsymm in
theorem grad_coeff (x : R3) (ξ : Fin 3 → ℝ) :
    Mgrad a (fun j z => τ * Xs a ψ lam j z) x ξ + 2 * κ * (τ * θs ψ lam x) * quad a x ξ =
      τ * lam * phi ψ lam x * (4 * lam * (∑ j, bv a ψ j x * ξ j) ^ 2 + E1 a ψ x ξ +
        2 * κ * lam * quad a x ξ) := by
  have := contDiff_bv ha hψ
  simp only [Mgrad, Xs, θs]
  simp (disch := fun_prop) only [pd_const_mul, pd_mul, pd_phi hψ]
  simp only [E1, quad, bv_apply, Fin.sum_univ_three, hsymm 1 0, hsymm 2 0, hsymm 2 1]
  ring

theorem zero_coeff (x : R3) :
    mzero a (fun j z => τ * Xs a ψ lam j z)
        (fun z => τ ^ 2 * (lam ^ 2 * phi ψ lam z ^ 2 * Nf a ψ z)) x -
      κ * Lop a (fun z => τ * θs ψ lam z) x -
      2 * κ * (τ * θs ψ lam x) * (τ ^ 2 * (lam ^ 2 * phi ψ lam x ^ 2 * Nf a ψ x)) -
      κ * (τ * θs ψ lam x) ^ 2 =
    τ ^ 3 * (lam ^ 3 * phi ψ lam x ^ 3 *
        (4 * lam * Nf a ψ x ^ 2 + 2 * Pf a ψ x - 2 * κ * lam * Nf a ψ x)) -
      τ ^ 2 * (κ * lam ^ 4 * phi ψ lam x ^ 2) - τ * Rf a ψ lam κ x := by
  have := contDiff_bv ha hψ
  have hN := contDiff_Nf ha hψ
  have hXs : ∀ j, ContDiff ℝ ∞ (Xs a ψ lam j) := by
    intro j; unfold Xs; fun_prop
  have hθs : ContDiff ℝ ∞ (θs ψ lam) := by unfold θs; fun_prop
  simp only [mzero, divV_smul hXs, Lop_smul ha (contDiff_divV hXs), Lop_smul ha hθs, Rf]
  simp (disch := fun_prop) only [pd_const_mul, pd_mul, pd_phi hψ, pd_sq]
  simp only [Xs, θs, Pf, Nf_apply, Fin.sum_univ_three]
  ring

end spec

@[fun_prop] theorem contDiff_Lop {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Lop a f) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold Lop; fun_prop

/-! ### Elementary inequalities used in the final assembly -/

theorem grad_part_nonneg {τ lam φ bξ E Qd α C₁ κ n : ℝ} (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (hφ : 0 ≤ φ) (hE : |E| ≤ C₁ * n) (hQ : α * n ≤ Qd) (hκ : 0 ≤ κ)
    (hlarge : C₁ ≤ 2 * κ * lam * α) (hn : 0 ≤ n) :
    0 ≤ τ * lam * φ * (4 * lam * bξ ^ 2 + E + 2 * κ * lam * Qd) := by
  have h1 : 0 ≤ 4 * lam * bξ ^ 2 := by positivity
  have h2 : -(C₁ * n) ≤ E := (abs_le.1 hE).1
  have h3 : 2 * κ * lam * (α * n) ≤ 2 * κ * lam * Qd :=
    mul_le_mul_of_nonneg_left hQ (by positivity)
  have h4 : C₁ * n ≤ 2 * κ * lam * α * n := mul_le_mul_of_nonneg_right hlarge hn
  have : 0 ≤ 4 * lam * bξ ^ 2 + E + 2 * κ * lam * Qd := by linarith
  exact mul_nonneg (by positivity) this

theorem B_ge {lam N P κ n₀ C₂ : ℝ} (hn₀ : 0 < n₀) (hN : n₀ ≤ N) (hκN : κ * N ≤ n₀ ^ 2)
    (hP : |P| ≤ C₂) (hlam : (C₂ + n₀ ^ 2) / n₀ ^ 2 ≤ lam) (hlam0 : 0 ≤ lam) :
    2 * n₀ ^ 2 ≤ 4 * lam * N ^ 2 + 2 * P - 2 * κ * lam * N := by
  have hN2 : n₀ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hn₀.le hN 2
  have h1 : κ * N * lam ≤ N ^ 2 * lam := mul_le_mul_of_nonneg_right (hκN.trans hN2) hlam0
  have h2 : C₂ + n₀ ^ 2 ≤ lam * n₀ ^ 2 := (div_le_iff₀ (by positivity)).1 hlam
  have h3 : lam * n₀ ^ 2 ≤ lam * N ^ 2 := mul_le_mul_of_nonneg_left hN2 hlam0
  have h4 := neg_abs_le P
  linarith

theorem zero_part_ge_one {τ lam φ φ₀ φ₁ B n₀ κ R D : ℝ} (hn₀ : 0 < n₀) (hB : 2 * n₀ ^ 2 ≤ B)
    (hlam : 1 ≤ lam) (hφ₀ : 0 < φ₀) (hφ0 : φ₀ ≤ φ) (hφ1 : φ ≤ φ₁) (hκ : 0 ≤ κ) (hR : R ≤ D)
    (hD : 0 ≤ D) (hτ : 1 ≤ τ)
    (hτ' : κ * lam ^ 4 * φ₁ ^ 2 + D + 1 ≤ τ * (2 * n₀ ^ 2 * lam ^ 3 * φ₀ ^ 3)) :
    1 ≤ τ ^ 3 * (lam ^ 3 * φ ^ 3 * B) - τ ^ 2 * (κ * lam ^ 4 * φ ^ 2) - τ * R := by
  have hφ : 0 < φ := lt_of_lt_of_le hφ₀ hφ0
  have e1 : φ₀ ^ 3 ≤ φ ^ 3 := pow_le_pow_left₀ hφ₀.le hφ0 3
  have e2 : φ ^ 2 ≤ φ₁ ^ 2 := pow_le_pow_left₀ hφ.le hφ1 2
  have e3 : 2 * n₀ ^ 2 * lam ^ 3 * φ₀ ^ 3 ≤ lam ^ 3 * φ ^ 3 * B := by
    have : 2 * n₀ ^ 2 * lam ^ 3 * φ₀ ^ 3 = lam ^ 3 * φ₀ ^ 3 * (2 * n₀ ^ 2) := by ring
    rw [this]
    exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity)) hB (by positivity)
      (by positivity)
  have e4 : κ * lam ^ 4 * φ ^ 2 ≤ κ * lam ^ 4 * φ₁ ^ 2 :=
    mul_le_mul_of_nonneg_left e2 (by positivity)
  have hτ0 : 0 ≤ τ := by linarith
  have hτ2 : τ ≤ τ ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left e3 (pow_nonneg hτ0 3)
  have h4 := mul_le_mul_of_nonneg_left e4 (pow_nonneg hτ0 2)
  have h5 : τ * R ≤ τ * D := mul_le_mul_of_nonneg_left hR hτ0
  have h6 := mul_le_mul_of_nonneg_left hτ' (pow_nonneg hτ0 2)
  have h7 : τ * D ≤ τ ^ 2 * D := mul_le_mul_of_nonneg_right hτ2 hD
  have h8 : 1 ≤ τ ^ 2 := by nlinarith
  have h9 : τ ^ 2 * (τ * (2 * n₀ ^ 2 * lam ^ 3 * φ₀ ^ 3)) =
      τ ^ 3 * (2 * n₀ ^ 2 * lam ^ 3 * φ₀ ^ 3) := by ring
  linarith

end OAI.AnisotropicCalderon
