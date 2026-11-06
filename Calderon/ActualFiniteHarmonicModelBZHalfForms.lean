import Calderon.ActualFiniteHarmonicModelBDerivativeAngularForm
import Calderon.ActualFiniteHarmonicModelBDerivativeFormCoefficientBounds
import Calderon.ActualFiniteHarmonicModelBZScalarActions

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualModelCommutatorWords PrincipalCommutator AmbientReferenceRaising
  ConformalDepth ReferenceDensityBounds ReferenceWeightedApproximation NormalizedPrincipalMetric
  CoordinateBootstrapJets ActualReferenceDDHigherLogFrameJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev bzHalfFormsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] bzHalfFormsFunction
attribute [local irreducible] nativeB nativeZ

theorem exists_nativeBZ_uniform_half_threehalf_forms
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪(nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
        nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x,G x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ ∧
      ∀ k : Fin 3,
      |⟪(nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
        coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
          (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) F x,G x⟫_ℝ| ≤
        (C*eps*beta)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨CB,hCB,hBcoeff⟩ := exists_nativeB_derivative_form_coefficient_uniform_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK
  obtain ⟨J,hJ,hLog⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g1 hg1 L hL K hK 1
  refine ⟨3*J*CB,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j F G
  let H := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖
  let V := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖
  let B := nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hH : 0 ≤ H := norm_nonneg _
  have hV : 0 ≤ V := norm_nonneg _
  have hB (a : Fin 3) : |⟪B (coreDerivative hO hD hF a F) x,G x⟫_ℝ| ≤
      (CB*eps/beta)*H*V := by
    have ht := abs_inner_nativeB_coreDerivative_le_half_threehalf hO hD hF g1 g2 hg1
      L lam δ R p j a hg2 hδ hR F G x
    have hc := hBcoeff lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j
    exact ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hH) hV)
  have hsum (f : Fin 3 → ℝ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ a, |f a| ≤ M) :
      |∑ a : Fin 3, f a * ⟪B (coreDerivative hO hD hF a F) x,G x⟫_ℝ| ≤
        3*(M*(CB*eps/beta))*H*V := by
    calc
      _ ≤ ∑ a : Fin 3, |f a * ⟪B (coreDerivative hO hD hF a F) x,G x⟫_ℝ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Fin 3, M*((CB*eps/beta)*H*V) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [abs_mul]
        exact mul_le_mul (hf a) (hB a) (abs_nonneg _) hM
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  constructor
  · rw [nativeB_nativeZ_scalar_angular_action,sum_inner]
    simp only [real_inner_smul_left]
    have hf (a : Fin 3) : |referenceFrameDerivative g1 L lam a
        (fun y => Real.log (referenceRadius δ R p L y)) x| ≤ J*beta := by
      simpa only [ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one,beta,actualReferenceBeta] using
        (hLog lam hlam δ hδ hδ1 R hR p hp x hx hb [] (by simp)).1 a
    have ht := hsum _ (J*beta) (mul_nonneg hJ.le hbpos.le) hf
    calc
      _ ≤ 3*((J*beta)*(CB*eps/beta))*H*V := ht
      _ = _ := by field_simp; ring
  · intro k
    rw [nativeB_coefficientDerivative_nativeZ_scalar_angular_action,sum_inner]
    simp only [real_inner_smul_left]
    have hf (a : Fin 3) : |directionalFDeriv (coordinateDirection k)
        (referenceFrameDerivative g1 L lam a
          (fun y => Real.log (referenceRadius δ R p L y))) x| ≤ J*beta^2 := by
      simpa only [ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,beta,actualReferenceBeta] using
        (hLog lam hlam δ hδ hδ1 R hR p hp x hx hb [k] (by simp)).1 a
    have ht := hsum _ (J*beta^2) (mul_nonneg hJ.le (sq_nonneg beta)) hf
    calc
      _ ≤ 3*((J*beta^2)*(CB*eps/beta))*H*V := ht
      _ = _ := by field_simp; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
