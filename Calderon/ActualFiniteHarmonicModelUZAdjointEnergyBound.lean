import Calderon.ActualFiniteHarmonicModelUZEnergyBound

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev uzAdjointEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] uzAdjointEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ nativeU nativeUdag nativeZdag

lemma nativeUZ_adjoint_sum_density_pair_eq_twice
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) :
    nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
      ((nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
        nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR +
        nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR *
        nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F) =
    2 * nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
      ((nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
        nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F) := by
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  have ha : q ((nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F) =
      q ((nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR *
        nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F) := by
    have ht := compact_nativeUZ_adjoint hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F F
    simpa only [q,nativeCoreDensityPairLinearMap,LinearMap.coe_mk,AddHom.coe_mk,
      real_inner_comm] using ht
  change q (((_ : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) + _) F) =
    2*q ((_ : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) F)
  rw [LinearMap.add_apply,map_add,← ha]
  ring

theorem exists_nativeUZ_adjoint_sum_uniform_energy_bound
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
          nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR +
          nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR *
          nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hUZ⟩ := exists_nativeUZ_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨2*C,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have hq : |q ((nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F)| ≤ C*eps*J :=
    hUZ lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  change |nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F (((_ : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))+_) F)| ≤ _
  rw [nativeUZ_adjoint_sum_density_pair_eq_twice,abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2*(C*eps*J) := mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
