import Calderon.CurvatureContraction
import Calderon.CommonProfileFamily

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.HessianContraction
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial MvPolynomial
  FrameCurvaturePolynomial MetricVolume

lemma fischerInner_eq_sum_of_support_subset (p q : MvPolynomial (Fin 3) ℝ)
    (s : Finset (Fin 3 →₀ ℕ)) (hp : p.support ⊆ s) :
    fischerInner p q = ∑ a ∈ s, p.coeff a * q.coeff a * fischerWeight a := by
  classical
  unfold fischerInner
  apply Finset.sum_subset hp
  intro a ha hap
  simp [notMem_support_iff.mp hap]

def polynomialFamilySupport (q : Fin 3 → MvPolynomial (Fin 3) ℝ) : Finset (Fin 3 →₀ ℕ) :=
  Finset.univ.biUnion fun i => (q i).support

lemma support_subset_polynomialFamilySupport (q : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (i : Fin 3) : (q i).support ⊆ polynomialFamilySupport q := by
  classical
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,ha⟩

lemma fischer_matrix_contraction_eq_coeff_sum (H : Fin 3 → Fin 3 → ℝ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, H i j * fischerInner (q i) (q j)) =
      ∑ a ∈ polynomialFamilySupport q, fischerWeight a *
        (∑ i : Fin 3, ∑ j : Fin 3, H i j * (q i).coeff a * (q j).coeff a) := by
  classical
  simp_rw [fischerInner_eq_sum_of_support_subset _ _ (polynomialFamilySupport q)
    (support_subset_polynomialFamilySupport q _), Finset.mul_sum]
  have hswap (i : Fin 3) :
      (∑ j : Fin 3, ∑ a ∈ polynomialFamilySupport q,
        H i j * ((q i).coeff a * (q j).coeff a * fischerWeight a)) =
      ∑ a ∈ polynomialFamilySupport q, ∑ j : Fin 3,
        H i j * ((q i).coeff a * (q j).coeff a * fischerWeight a) :=
    Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma sum_fischerInner_self_eq_coeff_sum (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, fischerInner (q i) (q i)) =
      ∑ a ∈ polynomialFamilySupport q, fischerWeight a *
        (∑ i : Fin 3, ((q i).coeff a)^2) := by
  classical
  simp_rw [fischerInner_eq_sum_of_support_subset _ _ (polynomialFamilySupport q)
    (support_subset_polynomialFamilySupport q _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma fischer_matrix_contraction_le_of_quadratic (H : Fin 3 → Fin 3 → ℝ)
    (a : ℝ) (hH : ∀ c : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, H i j * c i * c j) ≤ -a * (∑ i : Fin 3, (c i)^2))
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, H i j * fischerInner (q i) (q j)) ≤
      -a * (∑ i : Fin 3, fischerInner (q i) (q i)) := by
  classical
  rw [fischer_matrix_contraction_eq_coeff_sum, sum_fischerInner_self_eq_coeff_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have h := mul_le_mul_of_nonneg_left (hH (fun i => (q i).coeff b))
    (fischerWeight_pos b).le
  convert h using 1 <;> ring

lemma metricFrame_square_sum (M : R3 →L[ℝ] R3) (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame M e) (c : Fin 3 → ℝ) :
    ⟪M (∑ i : Fin 3, c i • e i), ∑ i : Fin 3, c i • e i⟫_ℝ =
      ∑ i : Fin 3, (c i)^2 := by
  simp only [IsMetricOrthonormalFrame] at he
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, he]
  simp [pow_two]

lemma bilinear_metricFrame_quadratic (B : R3 →L[ℝ] R3 →L[ℝ] ℝ)
    (e : Fin 3 → R3) (c : Fin 3 → ℝ) :
    B (∑ i : Fin 3, c i • e i) (∑ i : Fin 3, c i • e i) =
      ∑ i : Fin 3, ∑ j : Fin 3, B (e i) (e j) * c i * c j := by
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma bilinear_fischer_contraction_le_of_metric_quadratic
    (B : R3 →L[ℝ] R3 →L[ℝ] ℝ) (M : R3 →L[ℝ] R3)
    (e : Fin 3 → R3) (he : IsMetricOrthonormalFrame M e) (a : ℝ)
    (hB : ∀ X : R3, B X X ≤ -a * ⟪M X,X⟫_ℝ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, B (e i) (e j) * fischerInner (q i) (q j)) ≤
      -a * (∑ i : Fin 3, fischerInner (q i) (q i)) := by
  apply fischer_matrix_contraction_le_of_quadratic _ a _ q
  intro c
  have h := hB (∑ i : Fin 3, c i • e i)
  rw [metricFrame_square_sum M e he, bilinear_metricFrame_quadratic B e] at h
  exact h

def referenceProfileHessianBilinear (g : MatrixField) (lam δ R : ℝ) (p : ℕ)
    (L : ℝ) (x : R3) : R3 →L[ℝ] R3 →L[ℝ] ℝ :=
  MetricVolume.coordinateHessianBilinear (referenceLogRadius δ R p L)
    (ConnectionError.coordinateConnectionField
      (inverseMetricOperator (referenceMetric (dilatedMetric g lam) L))
      (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) x) x

def referenceProfileHessianContraction (g : MatrixField) (lam δ R : ℝ) (p : ℕ)
    (L : ℝ) (x : R3) (e : Fin 3 → R3) (k : ℕ)
    (v : MvPolynomial (Fin 3) ℝ) : ℝ :=
  2*(k : ℝ)*(∑ i : Fin 3, ∑ j : Fin 3,
    referenceProfileHessianBilinear g lam δ R p L x (e i) (e j) *
      fischerInner (pderiv i v) (pderiv j v))

lemma referenceProfileHessianBilinear_le (g : MatrixField) (K : Set R3)
    (L c0 c1 J1 J2 D : ℝ) (hbounds : referenceProfileBounds g K L c0 c1 J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (x : R3) (hx : x ∈ K) (X : R3) :
    referenceProfileHessianBilinear g lam δ R p L x X X ≤
      -(c1 * referenceProfileNorm g lam δ R p L x)*
        ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) x X,X⟫_ℝ := by
  rw [referenceProfileHessianBilinear, MetricVolume.coordinateHessianBilinear_apply]
  have h := (hbounds.1 lam hlam δ hδ hδ1 R hR p hp x hx).2.1 X
  simpa only [neg_mul] using h

lemma referenceProfileHessianContraction_le (g : MatrixField) (K : Set R3)
    (L c0 c1 J1 J2 D : ℝ) (hbounds : referenceProfileBounds g K L c0 c1 J1 J2 D)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℝ) (hR : 0 < R) (p : ℕ) (hp : 1 ≤ p) (x : R3) (hx : x ∈ K)
    (e : Fin 3 → R3)
    (he : IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e)
    (k : ℕ) (v : MvPolynomial (Fin 3) ℝ) (hv : v.IsHomogeneous k) :
    referenceProfileHessianContraction g lam δ R p L x e k v ≤
      -2*c1*(k : ℝ)^2*referenceProfileNorm g lam δ R p L x*fischerInner v v := by
  have h := bilinear_fischer_contraction_le_of_metric_quadratic
    (referenceProfileHessianBilinear g lam δ R p L x) _ e he
    (c1*referenceProfileNorm g lam δ R p L x)
    (referenceProfileHessianBilinear_le g K L c0 c1 J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp x hx)
    (fun i => pderiv i v)
  rw [sum_fischerInner_pderiv_self hv] at h
  have hm := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2*(k : ℝ))
  unfold referenceProfileHessianContraction
  convert hm using 1 <;> ring

theorem exists_referenceProfileHessianContraction_uniform_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L c : ℝ, 0 < L ∧ 0 < c ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ k : ℕ, ∀ v : MvPolynomial (Fin 3) ℝ, v.IsHomogeneous k →
      referenceProfileHessianContraction g lam δ R p L x e k v ≤
        -2*c*(k : ℝ)^2*referenceProfileNorm g lam δ R p L x*fischerInner v v := by
  obtain ⟨L,c0,c1,J1,J2,D,hL,hc0,hc1,hJ1,hJ2,hD,hbounds⟩ := exists_referenceProfileBounds g hg K hK
  refine ⟨L,c1,hL,hc1,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx e he k v hv
  exact referenceProfileHessianContraction_le g K L c0 c1 J1 J2 D hbounds lam hlam δ hδ hδ1 R hR p hp x hx e he k v hv

theorem exists_referenceProfileHessianContraction_uniform_normalized_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L c : ℝ, 0 < L ∧ 0 < c ∧ ∀ hF : SphereHarmonic.SphereFischerInner,
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ e : Fin 3 → R3,
      IsMetricOrthonormalFrame (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x) e →
      ∀ k : ℕ, ∀ v : MvPolynomial (Fin 3) ℝ, v ∈ SphereHarmonic.harmonicHomogeneous k →
      referenceProfileHessianContraction g lam δ R p L x e k v / sphereNormalization 3 k ≤
        -2*c*(k : ℝ)^2*referenceProfileNorm g lam δ R p L x*‖SphereHarmonic.polynomialSphereL2 v‖^2 := by
  obtain ⟨L,c,hL,hc,hbound⟩ := exists_referenceProfileHessianContraction_uniform_bound g hg K hK
  refine ⟨L,c,hL,hc,?_⟩
  intro hF lam hlam δ hδ hδ1 R hR p hp x hx e he k v hv
  have h := div_le_div_of_nonneg_right (hbound lam hlam δ hδ hδ1 R hR p hp x hx e he k v hv.1)
    (sphereNormalization_pos (n := 3) (by norm_num : 0 < 3) k).le
  rw [SphereHarmonic.polynomialSphereL2_norm_sq hF k v hv]
  unfold normalizedFischerSquare normalizedFischerInner
  simpa only [Fintype.card_fin, mul_div_assoc] using h

end OAI.AnisotropicCalderon.HessianContraction
