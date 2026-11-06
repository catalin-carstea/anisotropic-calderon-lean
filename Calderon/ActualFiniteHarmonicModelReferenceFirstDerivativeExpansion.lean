import Calderon.ActualFiniteHarmonicModelReferenceFirstUniformExpansion
import Calderon.ActualFiniteHarmonicModelScalarOperatorHalfForms
import Calderon.ActualFiniteHarmonicModelCoefficientCore

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualModelCommutatorWords ReferenceDensityBounds PrincipalCommutator
  ActualMixedDensityHigherCoefficientJets ActualReferenceDDHigherGeometryJets
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma hasCoreScalarExpansionBound_referenceFirst_coefficientDerivative
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j k : Fin 3) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
        (nativeReferenceFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j)) x
      (∑ a : Fin 3, |directionalFDeriv (coordinateDirection k)
        (fun y => referenceMetricGramFrame g L (lam,y) a j) x|) := by
  unfold nativeReferenceFirstCoefficient
  rw [coefficientDerivative,ActualModelCommutatorWords.commutator_sum_right]
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  have he : Commute (coreRaising hO hD hF a) (nativeReferenceFrameScalar hO hD g hg L lam a j) := by
    unfold nativeReferenceFrameScalar
    exact scalarCentral_coreRaising hO hD hF a _ _
  rw [he.eq]
  change HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
    (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
      (nativeReferenceFrameScalar hO hD g hg L lam a j*coreRaising hO hD hF a)) x _
  have hd : Commute (coreDirectionalDerivative hO hD (coordinateDirection k)) (coreRaising hO hD hF a) :=
    (coreDirectionalDerivative_normalizedRaising_commute hO hD (coordinateDirection k) hF a).mul_right
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) (coordinateDirection k)).symm
  have hz : coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
      (coreRaising hO hD hF a) = 0 := sub_eq_zero.mpr hd.eq
  unfold nativeReferenceFrameScalar
  rw [coefficientDerivative_coreScalar_mul,hz,mul_zero,add_zero]
  exact hasCoreScalarExpansionBound_single hO hD (coreAngularGenerator hO hD hF)
    (Sum.inr (Sum.inl a)) _ _ x

theorem exists_nativeReferenceFirst_coefficientDerivative_uniform_linear_expansion
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ R : ℝ, ∀ p : ℕ, ∀ hδ : 0 < δ, ∀ hR : 0 < R,
      ∀ x ∈ K, ∀ j k : Fin 3,
      HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
          (nativeReferenceFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j)) x C := by
  obtain ⟨M,hM,hbound⟩ := exists_mixed_background_coordinate_jet_bound g hg L K hK 1
  refine ⟨3*M,by have hm : 0 < M := lt_of_lt_of_le zero_lt_one hM; positivity,?_⟩
  intro lam hlam δ R p hδ hR x hx j k
  have he := hasCoreScalarExpansionBound_referenceFirst_coefficientDerivative hO hD hF g hg L lam δ R p hδ hR j k x
  apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ _ he
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    (hbound lam hlam x hx).1 [k] (by simp) a j)
  simpa only [coordinateFieldWordPartial,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hs

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
