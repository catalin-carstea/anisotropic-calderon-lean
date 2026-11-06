import Calderon.ActualFiniteHarmonicModelBAngularPartUniform
import Calderon.ActualFiniteHarmonicModelHAngularPartUniform

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ReferenceWeightedApproximation CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativeBAngularPart_uniform_linear_expansion
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
      ∀ j : Fin 3,
      HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
        (nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) x (C*eps/beta) := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeBAngularPartMass_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j
  exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
    (hasCoreScalarExpansionBound_nativeBAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j x)
    (hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j)

theorem exists_nativeHAngularPart_uniform_linear_expansion
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
      ∀ j : Fin 3,
      HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
        (nativeHAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) x (C) := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeHAngularPartMass_uniform_bound g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j
  exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
    (hasCoreScalarExpansionBound_nativeHAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j x)
    (hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
