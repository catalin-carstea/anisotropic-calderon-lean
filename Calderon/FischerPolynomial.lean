import Calderon.AngularPolynomial
import Mathlib.Tactic

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def fischerWeight (a : σ →₀ ℕ) : ℝ := ∏ i : σ, (Nat.factorial (a i) : ℝ)

def fischerInner (p q : MvPolynomial σ ℝ) : ℝ :=
  p.coeff.sum fun a c => c * q.coeff a * fischerWeight a

lemma fischerInner_monomial_left (a : σ →₀ ℕ) (c : ℝ) (q : MvPolynomial σ ℝ) :
    fischerInner (monomial a c) q = c * q.coeff a * fischerWeight a := by
  simp [fischerInner]

lemma fischerInner_add_left (p q r : MvPolynomial σ ℝ) :
    fischerInner (p + q) r = fischerInner p r + fischerInner q r := by
  classical
  simp only [fischerInner, AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index (by simp) (by intros; ring)

lemma fischerInner_add_right (p q r : MvPolynomial σ ℝ) :
    fischerInner p (q + r) = fischerInner p q + fischerInner p r := by
  classical
  simp only [fischerInner, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    mul_add, add_mul, Finsupp.sum_add]

lemma fischerInner_symm (p q : MvPolynomial σ ℝ) :
    fischerInner p q = fischerInner q p := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | monomial b d =>
      classical
      simp only [fischerInner_monomial_left, coeff_monomial]
      by_cases h : a = b
      · subst b; simp only [ite_true]; ring
      · simp [h, Ne.symm h]
    | add p q hp hq => simp only [fischerInner_add_left, fischerInner_add_right, hp, hq]
  | add p q hp hq => simp only [fischerInner_add_left, fischerInner_add_right, hp, hq]

lemma fischerWeight_add_single (a : σ →₀ ℕ) (i : σ) :
    fischerWeight (a + Finsupp.single i 1) = (a i + 1 : ℝ) * fischerWeight a := by
  classical
  unfold fischerWeight
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  have hp : (∏ j ∈ Finset.univ \ {i},
      (Nat.factorial ((a + Finsupp.single i 1 : σ →₀ ℕ) j) : ℝ)) =
      ∏ j ∈ Finset.univ \ {i}, (Nat.factorial (a j) : ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using (Finset.mem_sdiff.mp hj).2
    simp [hji]
  rw [hp]
  simp [Nat.factorial_succ]
  ring

lemma fischerInner_X_mul_left (i : σ) (p q : MvPolynomial σ ℝ) :
    fischerInner (X i * p) q = fischerInner p (pderiv i q) := by
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [X, monomial_mul_monomial, one_mul, add_comm, fischerInner_monomial_left,
      fischerInner_monomial_left, coeff_pderiv, fischerWeight_add_single]
    ring
  | add p r hp hr =>
    simp only [mul_add, fischerInner_add_left, hp, hr]

lemma fischerInner_pderiv_left (i : σ) (p q : MvPolynomial σ ℝ) :
    fischerInner (pderiv i p) q = fischerInner p (X i * q) := by
  rw [fischerInner_symm, ← fischerInner_X_mul_left, fischerInner_symm]

lemma fischerInner_zero_left (p : MvPolynomial σ ℝ) : fischerInner 0 p = 0 := by
  simp [fischerInner]

lemma fischerInner_zero_right (p : MvPolynomial σ ℝ) : fischerInner p 0 = 0 := by
  rw [fischerInner_symm, fischerInner_zero_left]

lemma fischerInner_C_mul_right (c : ℝ) (p q : MvPolynomial σ ℝ) :
    fischerInner p (C c * q) = c * fischerInner p q := by
  classical
  simp only [fischerInner, coeff_C_mul, Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma fischerInner_C_mul_left (c : ℝ) (p q : MvPolynomial σ ℝ) :
    fischerInner (C c * p) q = c * fischerInner p q := by
  rw [fischerInner_symm, fischerInner_C_mul_right, fischerInner_symm p q]

lemma fischerInner_sum_right {ι : Type*} (s : Finset ι)
    (p : MvPolynomial σ ℝ) (q : ι → MvPolynomial σ ℝ) :
    fischerInner p (∑ i ∈ s, q i) = ∑ i ∈ s, fischerInner p (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fischerInner_zero_right]
  | insert i s hi ih => simp [hi, fischerInner_add_right, ih]

lemma fischerInner_nsmul_right (k : ℕ) (p q : MvPolynomial σ ℝ) :
    fischerInner p (k • q) = (k : ℝ) * fischerInner p q := by
  induction k with
  | zero => simp [fischerInner_zero_right]
  | succ k ih =>
    rw [succ_nsmul, fischerInner_add_right, ih]
    push_cast
    ring

theorem sum_fischerInner_pderiv_self {k : ℕ} {p : MvPolynomial σ ℝ}
    (hp : p.IsHomogeneous k) :
    (∑ i : σ, fischerInner (pderiv i p) (pderiv i p)) =
      (k : ℝ) * fischerInner p p := by
  simp_rw [fischerInner_pderiv_left]
  rw [← fischerInner_sum_right, hp.sum_X_mul_pderiv, fischerInner_nsmul_right]

lemma fischerWeight_pos (a : σ →₀ ℕ) : 0 < fischerWeight a := by
  classical
  exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos (a i)

lemma fischerInner_self_nonneg (p : MvPolynomial σ ℝ) : 0 ≤ fischerInner p p := by
  classical
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (mul_self_nonneg _) (le_of_lt (fischerWeight_pos a))

theorem fischerInner_self_eq_zero_iff (p : MvPolynomial σ ℝ) :
    fischerInner p p = 0 ↔ p = 0 := by
  classical
  constructor
  · intro hp
    have h : ∀ a ∈ p.support, p.coeff a * p.coeff a * fischerWeight a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        mul_nonneg (mul_self_nonneg _) (le_of_lt (fischerWeight_pos a)))).mp hp
    apply MvPolynomial.ext
    intro a
    by_cases ha : a ∈ p.support
    · have hz := h a ha
      have hw := ne_of_gt (fischerWeight_pos a)
      simpa [hw, mul_self_eq_zero] using hz
    · simp [notMem_support_iff.mp ha]
  · intro hp
    subst p
    exact fischerInner_zero_left 0

end OAI.AnisotropicCalderon.AngularPolynomial

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_pderiv_left
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.sum_fischerInner_pderiv_self
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_self_eq_zero_iff
