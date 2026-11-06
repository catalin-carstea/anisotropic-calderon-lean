import Calderon.ActualFiniteHarmonicModelCBalancedBounds
import Calderon.ActualFiniteHarmonicModelCBalancedNativeForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualReferenceDDHigherGeometryJets ReferenceWeightedApproximation ReferenceDensityBounds
  CoordinateBootstrapJets PrincipalCommutator ConformalDepth NormalizedPrincipalMetric
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWBoundsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWBoundsFunction
theorem exists_nativeC_coordinate_word_uniform_threehalf_half_form_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ w : List (Fin 3), w.length ≤ 2 →
      ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪coordinateFieldWordPartial w
          (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
          (coreWeightOperator hO hD (besselWeight 2) F x), G x⟫_ℝ| ≤
        ((C * eps) * beta^w.length) *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_nativeCSecondBalancedAngularCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall w hw F G
  rw [coordinateFieldWordPartial_nativeC_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR w F G x]
  let A := coordinateFieldWordPartial w (nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
  let U := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  let V := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  have hA : ‖A‖ ≤ (C*eps)*beta^w.length :=
    hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall w hw
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      ((A.le_opNorm U).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg U))) (norm_nonneg V))


theorem exists_nativeC_uniform_threehalf_half_form_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R, ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i k : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪(nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,G x⟫_ℝ| ≤
        (C * eps) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,G x⟫_ℝ| ≤
        ((C * eps) * beta) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪(ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i)) (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k)) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))) F x,G x⟫_ℝ| ≤
        ((C * eps) * beta^2) * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_nativeCSecondBalancedAngularCoefficient_uniform_coordinate_word_smallness
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k F G
  let WB := nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p
  let U := coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x
  let V := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  have h0 : ‖WB x‖ ≤ C*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp)
  have h1 : ‖directionalFDeriv (coordinateDirection i) WB x‖ ≤ (C*eps)*beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd,pow_one] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [i] (by simp)
  have h2 : ‖directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection k) WB) x‖ ≤ (C*eps)*beta^2 := by
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [i,k] (by simp)
  have hform (A : SphereL2 →L[ℝ] SphereL2) (B : ℝ) (hA : ‖A‖ ≤ B) :
      |⟪A U,V⟫_ℝ| ≤ B*‖U‖*‖V‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        ((A.le_opNorm U).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg U))) (norm_nonneg V))
  refine ⟨?_,?_,?_⟩
  · rw [nativeC_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F G x]
    exact hform (WB x) (C*eps) h0
  · rw [coefficientDerivative_nativeC_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i F G x]
    exact hform (directionalFDeriv (coordinateDirection i) WB x) ((C*eps)*beta) h1
  · rw [coefficientDerivative_second_nativeC_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i k F G x]
    exact hform (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) WB) x) ((C*eps)*beta^2) h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
