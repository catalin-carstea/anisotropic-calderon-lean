import Calderon.CurvatureContraction
import Calderon.PolynomialSlotCompatibility

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FullCovectorCurvature
open RadiusProfile ConformalDepth MetricOperator SphereHarmonic AngularPolynomial MvPolynomial
  CurvatureRotation CurvatureSkew FrameCurvaturePolynomial CurvatureContraction
  PolynomialSlotCompatibility

def referenceCovectorCurvaturePolynomial (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (i j : Fin 3) (W : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (l : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  referenceHorizontalCurvaturePolynomial g L lam x e i j (W l) -
    ∑ b : Fin 3, C (referenceCurvatureRotationCoefficient g L lam x e i j b l) * W b

def referenceBaseCovectorCurvatureContraction (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (p : MvPolynomial (Fin 3) ℝ) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3,
    referenceCurvatureRotationCoefficient g L lam x e i j b j *
      fischerInner (pderiv i p) (pderiv b p))

def referenceFullCovectorCurvatureContraction (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (p : MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, fischerInner (pderiv i p)
    (referenceCovectorCurvaturePolynomial g L lam x e i j (fun b => pderiv b p) j)

lemma referenceCovectorCurvaturePolynomial_partial (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (i j l : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    referenceCovectorCurvaturePolynomial g L lam x e i j (fun b => pderiv b p) l =
      pderiv l (referenceHorizontalCurvaturePolynomial g L lam x e i j p) := by
  have h := polynomialMatrixVectorField_partial_commutator
    (referenceCurvatureRotationCoefficient g L lam x e i j) p l
  simp only [referenceCovectorCurvaturePolynomial, referenceHorizontalCurvaturePolynomial,
    referenceCurvatureVectorFieldPolynomial]
  linear_combination h

lemma referenceFullCovectorCurvatureContraction_eq (g : MatrixField) (L lam : ℝ) (x : R3)
    (e : Fin 3 → R3) (p : MvPolynomial (Fin 3) ℝ) :
    referenceFullCovectorCurvatureContraction g L lam x e p =
      referenceCurvatureContraction g L lam x e p +
        referenceBaseCovectorCurvatureContraction g L lam x e p := by
  simp only [referenceFullCovectorCurvatureContraction, referenceCovectorCurvaturePolynomial,
    referenceCurvatureContraction, referenceBaseCovectorCurvatureContraction,
    fischerInner_sub_right, fischerInner_sum_right, fischerInner_C_mul_right,
    Finset.sum_sub_distrib]
  exact sub_eq_add_neg _ _

lemma abs_fischerInner_le_half_squares (p q : MvPolynomial (Fin 3) ℝ) :
    |fischerInner p q| ≤ (fischerInner p p + fischerInner q q) / 2 := by
  simpa only [one_pow, one_mul, div_eq_mul_inv, mul_comm] using
    abs_fischerInner_le_of_square_bound 1 (by norm_num) p q q (by simp)

lemma abs_base_covector_curvature_sum_le (c : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hc : ∀ i j b, |c i j b| ≤ B)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous k) :
    |-(∑ i : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3,
        c i j b * fischerInner (pderiv i p) (pderiv b p))| ≤
      (9*B)*(k : ℝ)*fischerInner p p := by
  have hcross (i j b : Fin 3) :
      |c i j b * fischerInner (pderiv i p) (pderiv b p)| ≤
        (B/2)*(fischerInner (pderiv i p) (pderiv i p) +
          fischerInner (pderiv b p) (pderiv b p)) := by
    rw [abs_mul]
    calc
      _ ≤ B * ((fischerInner (pderiv i p) (pderiv i p) +
          fischerInner (pderiv b p) (pderiv b p))/2) :=
        mul_le_mul (hc i j b) (abs_fischerInner_le_half_squares _ _) (abs_nonneg _) hB
      _ = _ := by ring
  rw [abs_neg]
  calc
    _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, ∑ b : Fin 3,
        c i j b * fischerInner (pderiv i p) (pderiv b p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3,
        |c i j b * fischerInner (pderiv i p) (pderiv b p)| := by
      apply Finset.sum_le_sum; intro i hi
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum; intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3, (B/2)*
        (fischerInner (pderiv i p) (pderiv i p) +
          fischerInner (pderiv b p) (pderiv b p)) := by
      apply Finset.sum_le_sum; intro i hi
      apply Finset.sum_le_sum; intro j hj
      apply Finset.sum_le_sum; intro b hb
      exact hcross i j b
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul,
        sum_fischerInner_pderiv_self hp]
      ring

theorem exists_referenceBaseCovectorCurvatureContraction_uniform_fischer_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ k : ℕ, ∀ p : MvPolynomial (Fin 3) ℝ, p.IsHomogeneous k →
      |referenceBaseCovectorCurvatureContraction g L lam x e p| ≤
        C*(k : ℝ)*fischerInner p p := by
  obtain ⟨B,hB,hbound⟩ := exists_referenceCurvatureRotationCoefficient_uniform_bound g hg L hL K hK
  refine ⟨9*B,by positivity,?_⟩
  intro lam hlam x hx e he k p hp
  exact abs_base_covector_curvature_sum_le
    (fun i j b => referenceCurvatureRotationCoefficient g L lam x e i j b j)
    B hB.le (fun i j b => hbound lam hlam x hx e he i j b j) k p hp

theorem exists_referenceFullCovectorCurvatureContraction_uniform_fischer_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      |referenceFullCovectorCurvatureContraction g L lam x e p| ≤
        C*(k : ℝ)^2*fischerInner p p := by
  obtain ⟨A,hA,hpoly⟩ := exists_referenceCurvatureContraction_uniform_fischer_bound g hg L hL K hK
  obtain ⟨B,hB,hbase⟩ := exists_referenceBaseCovectorCurvatureContraction_uniform_fischer_bound g hg L hL K hK
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro hF lam hlam x hx e he k hk p hp
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkk : (k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  rw [referenceFullCovectorCurvatureContraction_eq]
  calc
    _ ≤ |referenceCurvatureContraction g L lam x e p| +
        |referenceBaseCovectorCurvatureContraction g L lam x e p| := abs_add_le _ _
    _ ≤ A*(k : ℝ)^2*fischerInner p p + B*(k : ℝ)*fischerInner p p :=
      add_le_add (hpoly hF lam hlam x hx e he k hk p hp) (hbase lam hlam x hx e he k p hp.1)
    _ ≤ A*(k : ℝ)^2*fischerInner p p + B*(k : ℝ)^2*fischerInner p p := by
      gcongr
      exact fischerInner_self_nonneg _
    _ = _ := by ring

theorem exists_referenceFullCovectorCurvatureContraction_uniform_normalized_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ hF : SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ k : ℕ, 1 ≤ k → ∀ p : MvPolynomial (Fin 3) ℝ,
      p ∈ harmonicHomogeneous k →
      |referenceFullCovectorCurvatureContraction g L lam x e p| / sphereNormalization 3 k ≤
        C*(k : ℝ)^2*‖polynomialSphereL2 p‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_referenceFullCovectorCurvatureContraction_uniform_fischer_bound g hg L hL K hK
  refine ⟨C,hC,?_⟩
  intro hF lam hlam x hx e he k hk p hp
  have h := div_le_div_of_nonneg_right (hbound hF lam hlam x hx e he k hk p hp)
    (sphereNormalization_pos (n := 3) (by norm_num : 0 < 3) k).le
  rw [polynomialSphereL2_norm_sq hF k p hp]
  unfold normalizedFischerSquare normalizedFischerInner
  simpa only [Fintype.card_fin, mul_div_assoc] using h

lemma referenceCurvatureContraction_eq_zero_of_isHomogeneous_one
    (g : MatrixField) (L lam : ℝ) (x : R3) (e : Fin 3 → R3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 1) :
    referenceCurvatureContraction g L lam x e p = 0 := by
  have hd (i : Fin 3) : (pderiv i p).IsHomogeneous 0 := by simpa using hp.pderiv (i := i)
  simp only [referenceCurvatureContraction,
    referenceHorizontalCurvaturePolynomial_eq_zero_of_isHomogeneous_zero g L lam x e _ _ _ (hd _),
    fischerInner_zero_right, Finset.sum_const_zero]

end OAI.AnisotropicCalderon.FullCovectorCurvature
