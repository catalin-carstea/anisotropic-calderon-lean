import Calderon.ActualFiniteHarmonicModelWPolynomialPart
import Calderon.ActualFiniteHarmonicModelReferenceTraceZeroMassBounds
import Calderon.ActualFiniteHarmonicModelDriftZeroMassBounds
import Calderon.ActualFiniteHarmonicModelMixedZeroScalarJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ReferenceWeightedApproximation
  CoordinateBootstrapJets ConformalDepth ActualHorizontalNormBridge
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherGeometryJets ActualPhysicalMixedReferenceCancellation
  NormalizedPrincipalMetricSmooth ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativeWPolynomialPartMass_uniform_smallness
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*referenceRadius δ R p L x →
      referenceRadius δ R p L x*beta^2 ≤ eps →
      nativeWPolynomialPartMass g1 g2 L lam δ R p x ≤ C*eps := by
  obtain ⟨CK,hCK,hKbound⟩ := exists_nativeReferenceTraceZeroRawMass_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CJ,hCJ,hJbound⟩ := exists_nativeDriftZeroRawMass_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CM,hCM,hMixed⟩ := exists_native_mixed_zero_coefficients_uniform_coordinate_word_smallness g1 g2 hg1 hg2 L hL K hK
  refine ⟨2*CK+84*CM+2*CJ,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hk := hKbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall
  have hj := hJbound lam hlam δ hδ hδ1 R hR p hp eps heps x hx hb hsmall
  have hd0 (a : Fin 3) : |physicalMixedDensityCorrection g1 L lam h a x| ≤ CM*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      (hMixed lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall a 0 0 [] (by simp)).1
  have hp0 (a : Fin 3) : |physicalMixedProfileCoefficient g1 L lam δ R p h a x| ≤ CM*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      (hMixed lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall a 0 0 [] (by simp)).2.1
  have hc0 (a b c : Fin 3) : |physicalMixedConnectionCoefficient g1 L lam h a b c x| ≤ CM*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      (hMixed lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall a b c [] (by simp)).2.2.1
  have hu0 (a b : Fin 3) : |physicalPureAngularCoefficient g1 L lam δ R p h a b x| ≤ CM*eps := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      (hMixed lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall a b 0 [] (by simp)).2.2.2
  have hds := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => hd0 a)
  have hps := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => hp0 a)
  have hcs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) =>
      Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin 3))) => hc0 a b c)))
  have hus := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) => hu0 a b))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hds hps hcs hus
  unfold nativeWPolynomialPartMass
  dsimp only
  simp only [← Finset.sum_mul]
  change nativeReferenceTraceZeroRawMass g1 L lam δ R p h x ≤ CK*eps at hk
  nlinarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
