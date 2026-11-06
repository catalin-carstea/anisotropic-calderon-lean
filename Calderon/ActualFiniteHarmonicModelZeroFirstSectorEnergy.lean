import Calderon.ActualFiniteHarmonicModelH0AngularEnergy
import Calderon.ActualFiniteHarmonicModelBDH0Energy
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
private abbrev h0bSectorEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] h0bSectorEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeH0B_commutator_uniform_energy_bound
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
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K → ∀ l i : Fin 3,
      |∫ x : R3, referenceDensityFamily g1 L (lam,x) *
        ⟪ActualModelCommutatorWords.commutator
          (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
          (nativeB hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR *
            coreDirectionalDerivative hO hD (coordinateDirection i)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CA,hCA,hAngular⟩ := exists_nativeH0_B_gradient_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CD,hCD,hDerivative⟩ := exists_nativeB_coefficientDerivative_H0_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨CA+CD,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i
  let H := nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let C0 := nativeB hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let d := coreDirectionalDerivative hO hD (coordinateDirection i)
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have ha : |q ((ActualModelCommutatorWords.commutator H C0*d) F)| ≤ (CA*eps)*J :=
    hAngular lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall l i F hsupp
  have hd : |q ((C0*coefficientDerivative d H) F)| ≤ (CD*eps)*J :=
    hDerivative lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall l i F hsupp
  change |q (ActualModelCommutatorWords.commutator H (C0*d) F)| ≤ _
  rw [commutator_zero_first d H C0]
  simp only [LinearMap.sub_apply,map_sub]
  calc
    _ ≤ |q ((ActualModelCommutatorWords.commutator H C0*d) F)|+|q ((C0*coefficientDerivative d H) F)| := abs_sub _ _
    _ ≤ (CA*eps)*J+(CD*eps)*J := add_le_add ha hd
    _ = _ := by ring

theorem exists_native_zero_first_sector_uniform_energy_bound
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
          (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
          (∑ l : Fin 3, nativeB hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR *
            coreDirectionalDerivative hO hD (coordinateDirection l)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hPair⟩ := exists_nativeH0B_commutator_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨3*C,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let H (l : Fin 3) := nativeB hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR*
    coreDirectionalDerivative hO hD (coordinateDirection l)
  let C0 := nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have hpair (l : Fin 3) : |q (ActualModelCommutatorWords.commutator C0 (H l) F)| ≤ (C*eps)*J :=
    hPair lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l l
  change |q (ActualModelCommutatorWords.commutator C0 (∑ l : Fin 3, H l) F)| ≤ _
  rw [ActualModelCommutatorWords.commutator_sum_right]
  simp only [LinearMap.sum_apply,map_sum]
  calc
    _ ≤ ∑ l : Fin 3, |q (ActualModelCommutatorWords.commutator C0 (H l) F)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin 3, (C*eps)*J := Finset.sum_le_sum (fun l _ => hpair l)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
