import Calderon.ActualFiniteHarmonicModelUZSecondBaseEnergyBound
import Calderon.ActualFiniteHarmonicModelUZFirstBaseEnergyBound
import Calderon.ActualFiniteHarmonicModelUZZeroBaseEnergyBound
import Calderon.ActualFiniteHarmonicModelUZThreeBaseSourceDecomposition

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev uzEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] uzEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeUZ_uniform_energy_bound
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
        ⟪(nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
          nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C2,hC2,h2⟩ := exists_nativeUZSecondBaseOperator_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨C1,hC1,h1⟩ := exists_nativeUZFirstBaseOperator_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨C0,hC0,h0⟩ := exists_nativeUZZeroBaseOperator_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C2+C1+C0,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  let S2 := nativeUZSecondBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let S1 := nativeUZFirstBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let S0 := nativeUZZeroBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hq2 : |q (S2 F)| ≤ C2*eps*J := h2 lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hq1 : |q (S1 F)| ≤ C1*eps*J := h1 lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hq0 : |q (S0 F)| ≤ C0*eps*J := h0 lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  change |q ((nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
    nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F)| ≤ _
  rw [nativeU_mul_nativeZ_eq_three_base_source]
  change |q ((S2+S1+S0) F)| ≤ _
  simp only [LinearMap.add_apply,map_add]
  calc
    _ ≤ |q (S2 F)+q (S1 F)|+|q (S0 F)| := abs_add_le _ _
    _ ≤ (|q (S2 F)|+|q (S1 F)|)+|q (S0 F)| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (C2*eps*J+C1*eps*J)+C0*eps*J := add_le_add (add_le_add hq2 hq1) hq0
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
