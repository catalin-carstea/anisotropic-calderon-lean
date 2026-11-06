import Calderon.FischerPolynomial

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

lemma fischerInner_sum_left {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial σ ℝ) (q : MvPolynomial σ ℝ) :
    fischerInner (∑ i ∈ s, p i) q = ∑ i ∈ s, fischerInner (p i) q := by
  rw [fischerInner_symm, fischerInner_sum_right]
  simp_rw [fischerInner_symm q]

lemma fischerInner_neg_right (p q : MvPolynomial σ ℝ) :
    fischerInner p (-q) = -fischerInner p q := by
  simpa using fischerInner_C_mul_right (-1) p q

lemma fischerInner_sub_right (p q r : MvPolynomial σ ℝ) :
    fischerInner p (q - r) = fischerInner p q - fischerInner p r := by
  simp [sub_eq_add_neg, fischerInner_add_right, fischerInner_neg_right]

lemma fischerInner_sub_left (p q r : MvPolynomial σ ℝ) :
    fischerInner (p - q) r = fischerInner p r - fischerInner q r := by
  rw [fischerInner_symm, fischerInner_sub_right, fischerInner_symm r p,
    fischerInner_symm r q]

lemma fischerInner_radiusSq_mul_left (p q : MvPolynomial σ ℝ) :
    fischerInner (radiusSq * p) q = fischerInner p (laplacian q) := by
  classical
  simp only [radiusSq, Finset.sum_mul, fischerInner_sum_left, laplacian,
    fischerInner_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_two, mul_assoc, fischerInner_X_mul_left, fischerInner_X_mul_left]

lemma fischerInner_radiusSq_mul_right (p q : MvPolynomial σ ℝ) :
    fischerInner p (radiusSq * q) = fischerInner (laplacian p) q := by
  rw [fischerInner_symm, fischerInner_radiusSq_mul_left, fischerInner_symm]

lemma pderiv_pderiv_comm (i j : σ) (p : MvPolynomial σ ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  apply MvPolynomial.ext
  intro a
  simp only [coeff_pderiv]
  have ha : a + Finsupp.single i 1 + Finsupp.single j 1 =
      a + Finsupp.single j 1 + Finsupp.single i 1 := by abel
  rw [ha]
  simp [Finsupp.single_apply, hij, Ne.symm hij]
  ring

lemma laplacian_pderiv (i : σ) (p : MvPolynomial σ ℝ) :
    laplacian (pderiv i p) = pderiv i (laplacian p) := by
  classical
  simp only [laplacian, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pderiv_pderiv_comm j i, pderiv_pderiv_comm j i]

lemma laplacian_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℝ) :
    laplacian (∑ i ∈ s, p i) = ∑ i ∈ s, laplacian (p i) := by
  classical
  simp only [laplacian, map_sum]
  exact Finset.sum_comm

def polynomialDivergence (q : σ → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, pderiv i (q i)

def polynomialRaising (q : σ → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, X i * q i

lemma laplacian_polynomialDivergence (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, laplacian (q i) = 0) :
    laplacian (polynomialDivergence q) = 0 := by
  classical
  simp [polynomialDivergence, laplacian_sum, laplacian_pderiv, hq]

lemma polynomialDivergence_isHomogeneous {k : ℕ} (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, (q i).IsHomogeneous k) :
    (polynomialDivergence q).IsHomogeneous (k - 1) := by
  exact IsHomogeneous.sum _ _ _ fun i _ => (hq i).pderiv

lemma pderiv_pderiv_X_mul [DecidableEq σ] (i j : σ) (p : MvPolynomial σ ℝ) :
    pderiv j (pderiv j (X i * p)) = X i * pderiv j (pderiv j p) +
      if j = i then 2 * pderiv j p else 0 := by
  classical
  by_cases h : j = i
  · subst j
    simp only [pderiv_mul, map_add, pderiv_X_self, one_mul, ite_true]
    ring
  · simp [pderiv_mul, pderiv_X, Pi.single_apply, h, Ne.symm h]

lemma laplacian_X_mul (i : σ) (p : MvPolynomial σ ℝ) :
    laplacian (X i * p) = X i * laplacian p + 2 * pderiv i p := by
  classical
  simp only [laplacian, pderiv_pderiv_X_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  simp

lemma laplacian_polynomialRaising (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, laplacian (q i) = 0) :
    laplacian (polynomialRaising q) = 2 * polynomialDivergence q := by
  classical
  simp [polynomialRaising, polynomialDivergence, laplacian_sum, laplacian_X_mul,
    hq, ← Finset.mul_sum]

def harmonicRaising (m : ℕ) (q : σ → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  polynomialRaising q -
    C (2 / (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))) * radiusSq *
      polynomialDivergence q

lemma radiusSq_isHomogeneous : (radiusSq : MvPolynomial σ ℝ).IsHomogeneous 2 := by
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow (R := ℝ) i 2

lemma polynomialRaising_isHomogeneous {k : ℕ} (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, (q i).IsHomogeneous k) :
    (polynomialRaising q).IsHomogeneous (k + 1) := by
  apply IsHomogeneous.sum
  intro i hi
  simpa [Nat.add_comm] using (isHomogeneous_X (R := ℝ) i).mul (hq i)

theorem harmonicRaising_isHomogeneous {k : ℕ} (hk : 1 ≤ k)
    (q : σ → MvPolynomial σ ℝ) (hq : ∀ i, (q i).IsHomogeneous k) :
    (harmonicRaising (k - 1) q).IsHomogeneous (k + 1) := by
  have hh : (radiusSq * polynomialDivergence q).IsHomogeneous (k + 1) := by
    convert radiusSq_isHomogeneous.mul (polynomialDivergence_isHomogeneous q hq) using 1
    omega
  rw [harmonicRaising, mul_assoc]
  exact (polynomialRaising_isHomogeneous q hq).sub (hh.C_mul _)

lemma radiusSq_laplacian_coefficient_pos [Nonempty σ] (m : ℕ) :
    0 < 4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ) := by
  have hn : 0 < (Fintype.card σ : ℝ) := by exact_mod_cast Fintype.card_pos
  positivity

lemma harmonicRaising_denominator_eq {k : ℕ} (hk : 1 ≤ k) :
    4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card σ : ℝ) =
      4 * ((k : ℝ) + (Fintype.card σ : ℝ) / 2 - 1) := by
  rw [Nat.cast_sub hk]
  push_cast
  ring

lemma harmonicRaising_norm_coefficient_eq {k : ℕ} (hk : 1 ≤ k) :
    4 / (4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card σ : ℝ)) =
      ((k : ℝ) + (Fintype.card σ : ℝ) / 2 - 1)⁻¹ := by
  rw [harmonicRaising_denominator_eq hk]
  norm_num [div_eq_mul_inv, mul_inv_rev]
  ring

lemma harmonicRaising_correction_coefficient_eq {k : ℕ} (hk : 1 ≤ k) :
    2 / (4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card σ : ℝ)) =
      (2 * ((k : ℝ) + (Fintype.card σ : ℝ) / 2 - 1))⁻¹ := by
  rw [harmonicRaising_denominator_eq hk]
  norm_num [div_eq_mul_inv, mul_inv_rev]
  ring

theorem laplacian_harmonicRaising {k : ℕ} (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, (q i).IsHomogeneous k) (hΔ : ∀ i, laplacian (q i) = 0)
    (hc : 4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card σ : ℝ) ≠ 0) :
    laplacian (harmonicRaising (k - 1) q) = 0 := by
  rw [harmonicRaising, mul_assoc, laplacian_sub, laplacian_polynomialRaising q hΔ,
    laplacian_C_mul, laplacian_radiusSq_mul_of_isHomogeneous
      (polynomialDivergence_isHomogeneous q hq), laplacian_polynomialDivergence q hΔ,
    mul_zero, zero_add, ← mul_assoc, ← map_mul]
  rw [div_mul_cancel₀ _ hc]
  simp only [map_ofNat, sub_self]

theorem fischerInner_harmonic_radiusSq_mul (h p : MvPolynomial σ ℝ)
    (hΔ : laplacian h = 0) : fischerInner h (radiusSq * p) = 0 := by
  rw [fischerInner_radiusSq_mul_right, hΔ, fischerInner_zero_left]

theorem fischerInner_radiusSq_self {m : ℕ} {s : MvPolynomial σ ℝ}
    (hs : s.IsHomogeneous m) (hΔ : laplacian s = 0) :
    fischerInner (radiusSq * s) (radiusSq * s) =
      (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ)) * fischerInner s s := by
  rw [fischerInner_radiusSq_mul_left, laplacian_radiusSq_mul_of_isHomogeneous hs,
    hΔ, mul_zero, zero_add, fischerInner_C_mul_right]

lemma fischerInner_X_mul_X_mul [DecidableEq σ] (i j : σ) (p q : MvPolynomial σ ℝ) :
    fischerInner (X i * p) (X j * q) =
      (if i = j then fischerInner p q else 0) +
      fischerInner (pderiv j p) (pderiv i q) := by
  classical
  rw [fischerInner_X_mul_left, pderiv_mul]
  by_cases h : i = j
  · subst j
    simp only [pderiv_X_self, one_mul, fischerInner_add_right, ite_true]
    rw [← fischerInner_pderiv_left]
  · simp [pderiv_X, Pi.single_apply, h, Ne.symm h, ← fischerInner_pderiv_left]

theorem fischerInner_polynomialRaising_self (q : σ → MvPolynomial σ ℝ) :
    fischerInner (polynomialRaising q) (polynomialRaising q) =
      (∑ i : σ, fischerInner (q i) (q i)) +
      ∑ i : σ, ∑ j : σ, fischerInner (pderiv j (q i)) (pderiv i (q j)) := by
  classical
  simp only [polynomialRaising, fischerInner_sum_left, fischerInner_sum_right,
    fischerInner_X_mul_X_mul, Finset.sum_add_distrib]
  simp
  exact Finset.sum_comm

theorem fischerInner_harmonicRaising_self {k : ℕ} (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, (q i).IsHomogeneous k) (hΔ : ∀ i, laplacian (q i) = 0)
    (hc : 4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card σ : ℝ) ≠ 0) :
    fischerInner (harmonicRaising (k - 1) q) (harmonicRaising (k - 1) q) =
      (∑ i : σ, fischerInner (q i) (q i)) +
      (∑ i : σ, ∑ j : σ, fischerInner (pderiv j (q i)) (pderiv i (q j))) -
      (4 / (4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card σ : ℝ))) *
        fischerInner (polynomialDivergence q) (polynomialDivergence q) := by
  have hcross : fischerInner (polynomialRaising q) (radiusSq * polynomialDivergence q) =
      2 * fischerInner (polynomialDivergence q) (polynomialDivergence q) := by
    rw [fischerInner_radiusSq_mul_right, laplacian_polynomialRaising q hΔ]
    simpa only [map_ofNat] using
      fischerInner_C_mul_left 2 (polynomialDivergence q) (polynomialDivergence q)
  have hnorm := fischerInner_radiusSq_self (polynomialDivergence_isHomogeneous q hq)
    (laplacian_polynomialDivergence q hΔ)
  simp only [harmonicRaising, mul_assoc, fischerInner_sub_left, fischerInner_sub_right,
    fischerInner_C_mul_left, fischerInner_C_mul_right]
  rw [hcross, fischerInner_symm (radiusSq * polynomialDivergence q), hcross, hnorm,
    fischerInner_polynomialRaising_self]
  field_simp [hc]
  <;> ring

end OAI.AnisotropicCalderon.AngularPolynomial

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.laplacian_harmonicRaising
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_radiusSq_self
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.fischerInner_harmonicRaising_self
