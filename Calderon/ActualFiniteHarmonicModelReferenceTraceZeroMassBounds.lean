import Calderon.ActualFiniteHarmonicModelReferenceTraceZeroRaw
import Calderon.ActualFiniteHarmonicModelCovectorZeroUniformMass
import Calderon.ActualReferenceDDHigherHCoframeJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ReferenceWeightedApproximation
  CoordinateBootstrapJets ConformalDepth ActualHorizontalNormBridge
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherGeometryJets ActualPhysicalMixedReferenceCancellation
  NormalizedPrincipalMetricSmooth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativeReferenceTraceZeroRawMass_uniform_smallness
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
      nativeReferenceTraceZeroRawMass g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ C*eps := by
  obtain ⟨Z,hZ,hzero⟩ := exists_nativeReferenceCovectorZeroRawMass_uniform_bound hO hD g1 hg1 L hL K hK
  obtain ⟨Q,hQ,hq⟩ := exists_physicalMixedFrameCoefficient_uniform_coordinate_word_bounds g1 hg1 L K hK 0 (by norm_num)
  refine ⟨9*(1+Q)*Z,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let r := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hz (a b : Fin 3) : nativeReferenceCovectorZeroRawMass g1 L lam δ R p a b x ≤ Z*beta^2 :=
    hzero lam hlam δ hδ hδ1 R hR p hp x hx hb a b
  have hqq (a b : Fin 3) : |physicalMixedQFrameCoefficient g1 L lam h a b x| ≤ 1+Q := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      (hq lam hlam δ R hδ hR p eps beta heps heps1 hb h
        (fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j)
        x hx hH8 hsmall a b [] (by simp)).2
  have hz0 (a b : Fin 3) : 0 ≤ nativeReferenceCovectorZeroRawMass g1 L lam δ R p a b x := by
    dsimp only [nativeReferenceCovectorZeroRawMass,nativeReferenceWeightedZeroRawMass,
      nativeReferenceConnectionDerivativeMass,nativeReferenceConnectionCoefficientMass]
    positivity
  have ht (a b : Fin 3) : |physicalMixedQFrameCoefficient g1 L lam h a b x| *
      nativeReferenceCovectorZeroRawMass g1 L lam δ R p a b x ≤ (1+Q)*(Z*beta^2) :=
    mul_le_mul (hqq a b) (hz a b) (hz0 a b) (by linarith)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
    Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) => ht a b))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  unfold nativeReferenceTraceZeroRawMass
  rw [abs_of_pos hr]
  calc
    _ ≤ r*(3*(3*((1+Q)*(Z*beta^2)))) := mul_le_mul_of_nonneg_left hs hr.le
    _ = (9*(1+Q)*Z)*(r*beta^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
