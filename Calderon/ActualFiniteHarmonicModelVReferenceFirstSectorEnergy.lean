import Calderon.ActualFiniteHarmonicModelVReferenceFirstDerivativeEnergy
import Calderon.ActualFiniteHarmonicModelReferenceFirstVDerivativeEnergy
import Calderon.ActualFiniteHarmonicModelVReferenceFirstSecondBaseEnergy
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
private abbrev vrFirstCommutatorEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] vrFirstCommutatorEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ

theorem exists_nativeV_referenceFirst_commutator_uniform_energy_bound
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
          (nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR *
            coreDirectionalDerivative hO hD (coordinateDirection l))
          (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i *
            coreDirectionalDerivative hO hD (coordinateDirection i)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CA,hCA,hAterm⟩ := exists_nativeV_referenceFirst_derivative_gradient_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CB,hCB,hBterm⟩ := exists_nativeReferenceFirst_V_derivative_gradient_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨C2,hC2,hSecond⟩ := exists_nativeV_referenceFirst_second_base_uniform_energy_bound
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C2+CA+CB,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i
  let beta := actualReferenceBeta g1 L lam δ R p
  let d (s : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection s)
  let H := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR
  let B := nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*finiteCoreSourceEnergy hO hD (beta x) F x
  have hpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hsec : |q ((ActualModelCommutatorWords.commutator H B*d l*d i) F)| ≤ (C2*eps)*J :=
    hSecond lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i l i
  have hA : |q ((H*coefficientDerivative (d l) B*d i) F)| ≤ (CA*eps)*J :=
    hAterm lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall l i l i F hsupp
  have hB : |q ((B*coefficientDerivative (d i) H*d l) F)| ≤ (CB*eps)*J :=
    hBterm lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall l i i l F hsupp
  change |q (ActualModelCommutatorWords.commutator (H*d l) (B*d i) F)| ≤ _
  rw [commutator_first_first (d l) (d i) H B (coreDirectionalDerivative_commute hO hD _ _)]
  simp only [LinearMap.sub_apply,LinearMap.add_apply,map_sub,map_add]
  calc
    _ ≤ |q ((ActualModelCommutatorWords.commutator H B*d l*d i) F)|+|q ((H*coefficientDerivative (d l) B*d i) F)|+
        |q ((B*coefficientDerivative (d i) H*d l) F)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (C2*eps)*J+(CA*eps)*J+(CB*eps)*J := add_le_add (add_le_add hsec hA) hB
    _ = _ := by ring


theorem exists_nativeV_referenceFirst_sector_uniform_energy_bound
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
        ⟪commutator
          (∑ l : Fin 3, nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR *
            coreDirectionalDerivative hO hD (coordinateDirection l))
          (∑ i : Fin 3, nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i *
            coreDirectionalDerivative hO hD (coordinateDirection i)) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hPair⟩ := exists_nativeV_referenceFirst_commutator_uniform_energy_bound
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨9*C,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let H (l : Fin 3) := nativeV hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR*
    coreDirectionalDerivative hO hD (coordinateDirection l)
  let B (i : Fin 3) := nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR i*
    coreDirectionalDerivative hO hD (coordinateDirection i)
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*
    finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have hpair (l i : Fin 3) : |q (commutator (H l) (B i) F)| ≤ (C*eps)*J :=
    hPair lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp l i
  change |q (commutator (∑ l : Fin 3, H l) (∑ i : Fin 3, B i) F)| ≤ _
  rw [ActualModelCommutatorWords.commutator_sum_left]
  simp only [ActualModelCommutatorWords.commutator_sum_right,LinearMap.sum_apply,map_sum]
  calc
    _ ≤ ∑ l : Fin 3, |∑ i : Fin 3, q (commutator (H l) (B i) F)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, |q (commutator (H l) (B i) F)| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ l : Fin 3, ∑ i : Fin 3, (C*eps)*J :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun i _ => hpair l i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
