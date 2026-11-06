import Calderon.ActualFiniteHarmonicModelWReferenceSectorEnergy
import Calderon.ActualFiniteHarmonicModelWReferenceZeroEnergy
import Calderon.ActualFiniteHarmonicModelFirstDefect
import Calderon.ActualFiniteHarmonicModelDensityPairLinearMap

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev wtEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] wtEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeW nativeT nativeReferenceFirstCoefficient nativeReferenceZeroCoefficient

theorem exists_nativeW_T_uniform_energy_bound
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
        ⟪ActualModelCommutatorWords.commutator
          (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
          (nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CA,hCA,hA⟩ := exists_nativeW_referenceFirst_sector_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CZ,hCZ,hZ⟩ := exists_nativeW_referenceZero_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨CA+CZ,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let W := nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let A := ∑ i : Fin 3, nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i * coreDirectionalDerivative hO hD (coordinateDirection i)
  let Z := nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have ha : |q (ActualModelCommutatorWords.commutator W A F)| ≤ (CA*eps)*J :=
    hA lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hz : |q (ActualModelCommutatorWords.commutator W Z F)| ≤ (CZ*eps)*J :=
    hZ lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  rw [nativeT_eq_modelFirstOrder]
  change |q (ActualModelCommutatorWords.commutator W (A+Z) F)| ≤ _
  rw [ActualModelCommutatorWords.commutator_add_right]
  simp only [LinearMap.add_apply,map_add]
  calc
    _ ≤ |q (ActualModelCommutatorWords.commutator W A F)|+|q (ActualModelCommutatorWords.commutator W Z F)| := abs_add_le _ _
    _ ≤ (CA*eps)*J+(CZ*eps)*J := add_le_add ha hz
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
