import Calderon.HarmonicRaising

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem two_mul_fischerInner_le (p q : MvPolynomial σ ℝ) :
    2 * fischerInner p q ≤ fischerInner p p + fischerInner q q := by
  have h := fischerInner_self_nonneg (p - q)
  simp only [fischerInner_sub_left, fischerInner_sub_right] at h
  rw [fischerInner_symm q p] at h
  linarith

theorem sum_fischerInner_pderiv_cross_le {k : ℕ} (q : σ → MvPolynomial σ ℝ)
    (hq : ∀ i, (q i).IsHomogeneous k) :
    (∑ i : σ, ∑ j : σ, fischerInner (pderiv j (q i)) (pderiv i (q j))) ≤
      (k : ℝ) * ∑ i : σ, fischerInner (q i) (q i) := by
  classical
  have hnorm : (∑ i : σ, ∑ j : σ,
      fischerInner (pderiv j (q i)) (pderiv j (q i))) =
      (k : ℝ) * ∑ i : σ, fischerInner (q i) (q i) := by
    calc
      _ = ∑ i : σ, (k : ℝ) * fischerInner (q i) (q i) :=
        Finset.sum_congr rfl fun i _ => sum_fischerInner_pderiv_self (hq i)
      _ = _ := by rw [Finset.mul_sum]
  have hswap : (∑ i : σ, ∑ j : σ,
      fischerInner (pderiv i (q j)) (pderiv i (q j))) =
      ∑ i : σ, ∑ j : σ, fischerInner (pderiv j (q i)) (pderiv j (q i)) :=
    Finset.sum_comm
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      two_mul_fischerInner_le (pderiv j (q i)) (pderiv i (q j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  simp only [hnorm] at hsum
  linarith

end OAI.AnisotropicCalderon.AngularPolynomial

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.two_mul_fischerInner_le
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.sum_fischerInner_pderiv_cross_le
