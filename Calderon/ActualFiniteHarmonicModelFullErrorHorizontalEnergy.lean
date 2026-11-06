import Calderon.ActualFiniteHarmonicModelFullErrorEnergy
import Calderon.ActualFiniteHarmonicModelHorizontalProfileIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  SectionFiveErrorForms BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev fullErrorHorizontalEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] fullErrorHorizontalEnergyFunction
attribute [local irreducible] finiteCoreReferenceProfileEnergy finiteCoreSourceEnergy nativeB nativeZ nativeU nativeUdag nativeT nativeTdag nativeH nativeH0 nativeC nativePrincipalCoefficient nativeFullErrorExpression

theorem exists_nativeFullErrorExpression_uniform_horizontal_energy_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CE,hCE,herror⟩ := exists_nativeFullErrorExpression_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CP,hCP,hprofile⟩ := exists_finiteCoreSourceEnergy_uniform_reference_profile_integral_bound hO hD g1 hg1 L K hK
  refine ⟨CE*CP,mul_pos hCE hCP,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hbeta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos (x : R3) := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hcompare := hprofile lam hlam _ hbeta hpos hb F hsupp
  calc
    _ ≤ (CE*eps)*∫ x : R3, referenceDensityFamily g1 L (lam,x)*
        finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x :=
      herror lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
    _ ≤ (CE*eps)*(CP*∫ x : R3, referenceDensityFamily g1 L (lam,x)*
        finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam (actualReferenceBeta g1 L lam δ R p x) F x) :=
      mul_le_mul_of_nonneg_left hcompare (mul_nonneg hCE.le heps)
    _ = _ := by ring


theorem exists_nativeReducedErrorExpression_uniform_horizontal_energy_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪nativeReducedErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeFullErrorExpression_uniform_horizontal_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  rw [← nativeFullErrorExpression_eq_reduced]
  exact hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp


theorem exists_nativeFullErrorCoefficientWords_uniform_horizontal_energy_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x) →
      (∀ x ∈ K, referenceRadius δ R p L x * (actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪nativeFullErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreReferenceProfileEnergy hO hD g1 hg1 L lam (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeFullErrorExpression_uniform_horizontal_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  rw [← nativeFullErrorExpression_eq_fullCoefficientWords]
  exact hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
