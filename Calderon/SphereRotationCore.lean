import Calderon.SphereElementaryCore

noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

def polynomialRotation (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := X i * pderiv j p - X j * pderiv i p

lemma polynomialRotation_harmonicHomogeneous (k : ℕ) (hk : 1 ≤ k) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    polynomialRotation i j p ∈ harmonicHomogeneous k := by
  refine ⟨?_, ?_⟩
  · have hi := (isHomogeneous_X (R := ℝ) i).mul (hp.1.pderiv (i := j))
    have hj := (isHomogeneous_X (R := ℝ) j).mul (hp.1.pderiv (i := i))
    have hdeg : 1 + (k - 1) = k := by omega
    simpa only [polynomialRotation, hdeg] using hi.sub hj
  · rw [polynomialRotation, laplacian_sub, laplacian_X_mul, laplacian_X_mul,
      laplacian_pderiv, laplacian_pderiv, hp.2, map_zero, map_zero, mul_zero,
      mul_zero, zero_add, zero_add, pderiv_pderiv_comm i j]
    exact sub_self _

lemma fischerInner_X_mul_square (i : Fin 3) (q : MvPolynomial (Fin 3) ℝ) :
    fischerInner (X i * q) (X i * q) =
      fischerInner q q + fischerInner (pderiv i q) (pderiv i q) := by
  rw [fischerInner_X_mul_left, pderiv_mul, pderiv_X_self, one_mul,
    fischerInner_add_right, ← fischerInner_pderiv_left]

lemma fischerInner_pderiv_square_le (k : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous k) :
    fischerInner (pderiv i p) (pderiv i p) ≤ (k : ℝ) * fischerInner p p := by
  rw [← sum_fischerInner_pderiv_self hp]
  exact Finset.single_le_sum (fun j _ => fischerInner_self_nonneg (pderiv j p))
    (Finset.mem_univ i)

lemma fischerInner_X_mul_pderiv_square_le (k : ℕ) (hk : 1 ≤ k) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous k) :
    fischerInner (X i * pderiv j p) (X i * pderiv j p) ≤
      (k : ℝ) ^ 2 * fischerInner p p := by
  rw [fischerInner_X_mul_square]
  have hD := fischerInner_pderiv_square_le k j p hp
  have hDD := fischerInner_pderiv_square_le (k - 1) i (pderiv j p) hp.pderiv
  rw [Nat.cast_sub hk] at hDD
  push_cast at hDD
  have hmul := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg k)
  nlinarith

lemma fischerInner_rotation_square_le (k : ℕ) (hk : 1 ≤ k) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous k) :
    fischerInner (polynomialRotation i j p) (polynomialRotation i j p) ≤
      (4 * (k : ℝ) ^ 2) * fischerInner p p := by
  have h1 := fischerInner_X_mul_pderiv_square_le k hk i j p hp
  have h2 := fischerInner_X_mul_pderiv_square_le k hk j i p hp
  have htri := fischerInner_self_add_le (X i * pderiv j p) (-(X j * pderiv i p))
  simp only [fischerInner_neg_left, fischerInner_neg_right, neg_neg,
    ← sub_eq_add_neg] at htri
  change fischerInner (X i * pderiv j p - X j * pderiv i p)
    (X i * pderiv j p - X j * pderiv i p) ≤ _
  nlinarith

lemma fischerInner_rotation_skew (i j : Fin 3) (p q : MvPolynomial (Fin 3) ℝ) :
    fischerInner (polynomialRotation i j p) q =
      -fischerInner p (polynomialRotation i j q) := by
  simp only [polynomialRotation, fischerInner_sub_left, fischerInner_sub_right,
    fischerInner_X_mul_left, fischerInner_pderiv_left]
  ring

lemma polynomialRotation_sphere_inner_skew (hF : SphereFischerInner)
    (k : ℕ) (hk : 1 ≤ k) (i j : Fin 3) (p q : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) (hq : q ∈ harmonicHomogeneous k) :
    ⟪polynomialSphereL2 (polynomialRotation i j p), polynomialSphereL2 q⟫_ℝ =
      -⟪polynomialSphereL2 p, polynomialSphereL2 (polynomialRotation i j q)⟫_ℝ := by
  rw [hF k _ q (polynomialRotation_harmonicHomogeneous k hk i j p hp) hq,
    hF k p _ hp (polynomialRotation_harmonicHomogeneous k hk i j q hq)]
  unfold normalizedFischerInner
  rw [fischerInner_rotation_skew, neg_div]

lemma polynomialRotation_sphere_norm_sq_le (hF : SphereFischerInner)
    (k : ℕ) (hk : 1 ≤ k) (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    ‖polynomialSphereL2 (polynomialRotation i j p)‖ ^ 2 ≤
      (4 * (k : ℝ) ^ 2) * ‖polynomialSphereL2 p‖ ^ 2 := by
  rw [polynomialSphereL2_norm_sq hF k _ (polynomialRotation_harmonicHomogeneous k hk i j p hp),
    polynomialSphereL2_norm_sq hF k p hp]
  unfold normalizedFischerSquare normalizedFischerInner
  have h := div_le_div_of_nonneg_right (fischerInner_rotation_square_le k hk i j p hp.1)
    (le_of_lt (sphereNormalization_pos (n := Fintype.card (Fin 3)) Fintype.card_pos k))
  convert h using 1 <;> ring

lemma polynomialRotation_sphere_norm_le (hF : SphereFischerInner)
    (k : ℕ) (hk : 1 ≤ k) (i j : Fin 3) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    ‖polynomialSphereL2 (polynomialRotation i j p)‖ ≤
      (2 * (k : ℝ)) * ‖polynomialSphereL2 p‖ := by
  have h := polynomialRotation_sphere_norm_sq_le hF k hk i j p hp
  have hn : 0 ≤ (2 * (k : ℝ)) * ‖polynomialSphereL2 p‖ := by positivity
  nlinarith [norm_nonneg (polynomialSphereL2 (polynomialRotation i j p)),
    norm_nonneg (polynomialSphereL2 p)]

def polynomialRotationCombination (c : Fin 3 → Fin 3 → ℝ)
    (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, C (c i j) * polynomialRotation i j p

lemma polynomialRotationCombination_harmonicHomogeneous (k : ℕ) (hk : 1 ≤ k)
    (c : Fin 3 → Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) :
    polynomialRotationCombination c p ∈ harmonicHomogeneous k := by
  classical
  apply (harmonicHomogeneous k).sum_mem
  intro i hi
  apply (harmonicHomogeneous k).sum_mem
  intro j hj
  simpa only [smul_eq_C_mul] using (harmonicHomogeneous k).smul_mem (c i j)
    (polynomialRotation_harmonicHomogeneous k hk i j p hp)

lemma polynomialRotationCombination_sphere_norm_le (hF : SphereFischerInner)
    (k : ℕ) (hk : 1 ≤ k) (c : Fin 3 → Fin 3 → ℝ)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    ‖polynomialSphereL2 (polynomialRotationCombination c p)‖ ≤
      (2 * (k : ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, |c i j|)) * ‖polynomialSphereL2 p‖ := by
  classical
  have hterm (i j : Fin 3) :
      ‖polynomialSphereL2 (C (c i j) * polynomialRotation i j p)‖ =
        |c i j| * ‖polynomialSphereL2 (polynomialRotation i j p)‖ := by
    rw [← smul_eq_C_mul, map_smul, norm_smul, Real.norm_eq_abs]
  calc
    _ = ‖∑ i : Fin 3, ∑ j : Fin 3,
        polynomialSphereL2 (C (c i j) * polynomialRotation i j p)‖ := by
      simp only [polynomialRotationCombination, map_sum]
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
        polynomialSphereL2 (C (c i j) * polynomialRotation i j p)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ‖polynomialSphereL2 (C (c i j) * polynomialRotation i j p)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        |c i j| * ‖polynomialSphereL2 (polynomialRotation i j p)‖ := by simp_rw [hterm]
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        |c i j| * ((2 * (k : ℝ)) * ‖polynomialSphereL2 p‖) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (polynomialRotation_sphere_norm_le hF k hk i j p hp) (abs_nonneg _)
    _ = _ := by simp only [← Finset.sum_mul]; ring

end OAI.AnisotropicCalderon.SphereHarmonic
