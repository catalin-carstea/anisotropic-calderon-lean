import Calderon.FrameCurvaturePolynomial

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CurvatureContraction
open RadiusProfile ConformalDepth MetricOperator SphereHarmonic AngularPolynomial MvPolynomial
  CurvatureRotation CurvatureSkew FrameCurvaturePolynomial

lemma pderiv_eq_zero_of_isHomogeneous_zero (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous 0) (i : Fin 3) : pderiv i p = 0 := by
  have hs := sum_fischerInner_pderiv_self hp
  simp only [Nat.cast_zero, zero_mul] at hs
  have hz : fischerInner (pderiv i p) (pderiv i p) = 0 := by
    have hle := Finset.single_le_sum (fun j _ => fischerInner_self_nonneg (pderiv j p))
      (Finset.mem_univ i)
    rw [hs] at hle
    exact le_antisymm hle (fischerInner_self_nonneg _)
  exact (fischerInner_self_eq_zero_iff _).mp hz

lemma polynomialRotation_eq_zero_of_isHomogeneous_zero (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous 0) (i j : Fin 3) : polynomialRotation i j p = 0 := by
  simp only [polynomialRotation, pderiv_eq_zero_of_isHomogeneous_zero p hp, mul_zero, sub_self]

lemma referenceHorizontalCurvaturePolynomial_eq_zero_of_isHomogeneous_zero
    (g : MatrixField) (L lam : ℝ) (x : R3) (e : Fin 3 → R3) (a b : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 0) :
    referenceHorizontalCurvaturePolynomial g L lam x e a b p = 0 := by
  simp only [referenceHorizontalCurvaturePolynomial, referenceCurvatureVectorFieldPolynomial,
    polynomialMatrixVectorField, pderiv_eq_zero_of_isHomogeneous_zero p hp,
    mul_zero, Finset.sum_const_zero, neg_zero]

lemma fischerInner_scaled_square (t : ℝ) (p q : MvPolynomial (Fin 3) ℝ) :
    fischerInner (C t * p + q) (C t * p + q) =
      t^2 * fischerInner p p + 2*t*fischerInner p q + fischerInner q q := by
  simp only [fischerInner_add_left, fischerInner_add_right, fischerInner_C_mul_left,
    fischerInner_C_mul_right, fischerInner_symm q p]
  ring

lemma abs_fischerInner_le_of_square_bound (t : ℝ) (ht : 0 < t)
    (p q r : MvPolynomial (Fin 3) ℝ)
    (hq : fischerInner q q ≤ t^2 * fischerInner r r) :
    |fischerInner p q| ≤ (t/2) * (fischerInner p p + fischerInner r r) := by
  have hp := fischerInner_self_nonneg (C t * p + q)
  have hm := fischerInner_self_nonneg (C (-t) * p + q)
  rw [fischerInner_scaled_square] at hp hm
  apply abs_le.mpr
  constructor <;> nlinarith

lemma fischerInner_square_bound_of_sphere_norm_bound (hF : SphereFischerInner)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (q r : MvPolynomial (Fin 3) ℝ)
    (hq : q ∈ harmonicHomogeneous m) (hr : r ∈ harmonicHomogeneous m)
    (hn : ‖polynomialSphereL2 q‖ ≤ t * ‖polynomialSphereL2 r‖) :
    fischerInner q q ≤ t^2 * fischerInner r r := by
  have hs : ‖polynomialSphereL2 q‖^2 ≤ t^2 * ‖polynomialSphereL2 r‖^2 := by
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).2 hn
    nlinarith only [hsq]
  rw [polynomialSphereL2_norm_sq hF m q hq, polynomialSphereL2_norm_sq hF m r hr] at hs
  unfold normalizedFischerSquare normalizedFischerInner at hs
  have hN := sphereNormalization_pos (n := 3) (by norm_num : 0 < 3) m
  have hs' : fischerInner q q / sphereNormalization 3 m ≤
      (t^2 * fischerInner r r) / sphereNormalization 3 m := by
    simpa only [Fintype.card_fin, mul_div_assoc] using hs
  exact (div_le_div_iff_of_pos_right hN).mp hs' 

lemma exists_referenceHorizontalCurvaturePolynomial_uniform_fischer_square_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ a b : Fin 3, ∀ m : ℕ, ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous m →
      fischerInner (referenceHorizontalCurvaturePolynomial g L lam x e a b p)
        (referenceHorizontalCurvaturePolynomial g L lam x e a b p) ≤
        (A * (m : ℝ))^2 * fischerInner p p := by
  obtain ⟨A,hA,hbound⟩ := exists_referenceHorizontalCurvaturePolynomial_uniform_sphere_norm_bound g hg L hL K hK
  refine ⟨A,hA,?_⟩
  intro hF lam hlam x hx e he a b m p hp
  by_cases hm : m = 0
  · subst m
    rw [referenceHorizontalCurvaturePolynomial_eq_zero_of_isHomogeneous_zero g L lam x e a b p hp.1]
    simp [fischerInner_zero_left]
  · have hm' : 1 ≤ m := by omega
    exact fischerInner_square_bound_of_sphere_norm_bound hF m (A*(m : ℝ)) (by positivity) _ p
      (referenceHorizontalCurvaturePolynomial_harmonicHomogeneous g hg L lam x e a b m hm' p hp)
      hp (hbound hF lam hlam x hx e he a b m hm' p hp)

def referenceCurvatureContraction (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (p : MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv i p)
    (referenceHorizontalCurvaturePolynomial g L lam x e i j (pderiv j p))

lemma pderiv_harmonicHomogeneous_pred (k : ℕ) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    pderiv i p ∈ harmonicHomogeneous (k-1) := by
  refine ⟨hp.1.pderiv, ?_⟩
  rw [laplacian_pderiv, hp.2, map_zero]

theorem exists_referenceCurvatureContraction_uniform_fischer_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      |referenceCurvatureContraction g L lam x e p| ≤
        C * (k : ℝ)^2 * fischerInner p p := by
  obtain ⟨A,hA,hbound⟩ := exists_referenceHorizontalCurvaturePolynomial_uniform_fischer_square_bound g hg L hL K hK
  refine ⟨3*A,by positivity,?_⟩
  intro hF lam hlam x hx e he k hk p hp
  have hk' : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hk)
  have hm : ((k-1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.sub_le k 1)
  have hsquare (i j : Fin 3) :
      fischerInner (referenceHorizontalCurvaturePolynomial g L lam x e i j (pderiv j p))
        (referenceHorizontalCurvaturePolynomial g L lam x e i j (pderiv j p)) ≤
        (A*(k : ℝ))^2 * fischerInner (pderiv j p) (pderiv j p) := by
    have h := hbound hF lam hlam x hx e he i j (k-1) (pderiv j p)
      (pderiv_harmonicHomogeneous_pred k j p hp)
    refine h.trans ?_
    gcongr
    exact fischerInner_self_nonneg _
  have hcross (i j : Fin 3) :
      |fischerInner (pderiv i p)
        (referenceHorizontalCurvaturePolynomial g L lam x e i j (pderiv j p))| ≤
        (A*(k : ℝ)/2)*(fischerInner (pderiv i p) (pderiv i p) +
          fischerInner (pderiv j p) (pderiv j p)) :=
    abs_fischerInner_le_of_square_bound (A*(k : ℝ)) (mul_pos hA hk') _ _ _ (hsquare i j)
  unfold referenceCurvatureContraction
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, fischerInner (pderiv i p)
        (referenceHorizontalCurvaturePolynomial g L lam x e i j (pderiv j p))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |fischerInner (pderiv i p)
        (referenceHorizontalCurvaturePolynomial g L lam x e i j (pderiv j p))| := by
      apply Finset.sum_le_sum; intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (A*(k : ℝ)/2)*
        (fischerInner (pderiv i p) (pderiv i p) + fischerInner (pderiv j p) (pderiv j p)) := by
      apply Finset.sum_le_sum; intro i hi
      apply Finset.sum_le_sum; intro j hj
      exact hcross i j
    _ = (3*A)*(k : ℝ)^2*fischerInner p p := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
        sum_fischerInner_pderiv_self hp.1]
      ring

theorem exists_referenceCurvatureContraction_uniform_normalized_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      |referenceCurvatureContraction g L lam x e p| / sphereNormalization 3 k ≤
        C * (k : ℝ)^2 * ‖polynomialSphereL2 p‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_referenceCurvatureContraction_uniform_fischer_bound g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro hF lam hlam x hx e he k hk p hp
  have h := div_le_div_of_nonneg_right (hbound hF lam hlam x hx e he k hk p hp)
    (sphereNormalization_pos (n := 3) (by norm_num : 0 < 3) k).le
  rw [polynomialSphereL2_norm_sq hF k p hp]
  unfold normalizedFischerSquare normalizedFischerInner
  simpa only [Fintype.card_fin, mul_div_assoc] using h

end OAI.AnisotropicCalderon.CurvatureContraction
