import Calderon.ActualFiniteHarmonicModelFullPrincipalEnergyBound
import Calderon.ActualFiniteHarmonicModelFirstFirstSectorEnergy
import Calderon.ActualFiniteHarmonicModelFirstZeroSectorEnergy
import Calderon.ActualFiniteHarmonicModelZeroFirstSectorEnergy
import Calderon.ActualFiniteHarmonicModelNativeWords
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ReferenceDensityBounds ReferenceWeightedApproximation PrincipalCommutator
  SectionFiveErrorForms BaseDensityAdjoint CoordinateBootstrapJets NormalizedPrincipalMetric ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev fullFirstDefectEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] fullFirstDefectEnergyFunction
attribute [local irreducible] finiteCoreSourceEnergy nativeB nativeZ nativeU nativeUdag nativeT nativeTdag nativeH nativeH0 nativeC nativePrincipalCoefficient

theorem exists_nativeFirstDefect_commutator_uniform_energy_bound
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
          (2 * (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR -
            nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) +
            (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR -
            nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
          (nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨CP,hCP,hP⟩ := exists_nativeFirstDefect_principal_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CFF,hCFF,hFF⟩ := exists_native_first_first_sector_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CZF,hCZF,hZF⟩ := exists_native_zero_first_sector_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CFZ,hCFZ,hFZ⟩ := exists_native_first_zero_sector_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CZZ,hCZZ,hZZ⟩ := exists_nativeH0_C_uniform_energy_integral_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨CP+CFF+CZF+CFZ+CZZ,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  let d (i : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection i)
  let H := ∑ i : Fin 3, nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR i*d i
  let H0 := nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let B := ∑ i : Fin 3, nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR*d i
  let P := ∑ i : Fin 3, ∑ j : Fin 3, nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j*d i*d j
  let C0 := nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let q := nativeCoreDensityPairLinearMap hO hD g1 hg1 L lam F
  let J := ∫ x : R3, referenceDensityFamily g1 L (lam,x)*finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x
  have hp0 : |q (ActualModelCommutatorWords.commutator (H+H0) P F)| ≤ (CP*eps)*J := by
    have ht := hP lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
    rw [nativeFirstDefect_eq_modelFirstOrder] at ht
    exact ht
  have hff : |q (ActualModelCommutatorWords.commutator H B F)| ≤ (CFF*eps)*J :=
    hFF lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hzf : |q (ActualModelCommutatorWords.commutator H0 B F)| ≤ (CZF*eps)*J :=
    hZF lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hfz : |q (ActualModelCommutatorWords.commutator H C0 F)| ≤ (CFZ*eps)*J :=
    hFZ lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have hzz : |q (ActualModelCommutatorWords.commutator H0 C0 F)| ≤ (CZZ*eps)*J :=
    hZZ lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  have halg {S : Type} [Ring S] (h h0 p b c : S) :
      ActualModelCommutatorWords.commutator (h+h0) (p+b+c)=
      ActualModelCommutatorWords.commutator (h+h0) p+
      ActualModelCommutatorWords.commutator h b+ActualModelCommutatorWords.commutator h0 b+
      ActualModelCommutatorWords.commutator h c+ActualModelCommutatorWords.commutator h0 c := by
    unfold ActualModelCommutatorWords.commutator
    noncomm_ring
  rw [nativeFirstDefect_eq_modelFirstOrder,nativeU_eq_modelSecondOrder]
  change |q (ActualModelCommutatorWords.commutator (H+H0) (P+B+C0) F)| ≤ _
  rw [halg H H0 P B C0]
  simp only [LinearMap.add_apply,map_add]
  let a := q (ActualModelCommutatorWords.commutator (H+H0) P F)
  let b := q (ActualModelCommutatorWords.commutator H B F)
  let c := q (ActualModelCommutatorWords.commutator H0 B F)
  let d0 := q (ActualModelCommutatorWords.commutator H C0 F)
  let e := q (ActualModelCommutatorWords.commutator H0 C0 F)
  change |a+b+c+d0+e| ≤ _
  calc
    _ ≤ |a|+|b|+|c|+|d0|+|e| := by
      linarith [abs_add_le a b,abs_add_le (a+b) c,abs_add_le (a+b+c) d0,abs_add_le (a+b+c+d0) e]
    _ ≤ (CP*eps)*J+(CFF*eps)*J+(CZF*eps)*J+(CFZ*eps)*J+(CZZ*eps)*J := by
      exact add_le_add (add_le_add (add_le_add (add_le_add hp0 hff) hzf) hfz) hzz
    _ = _ := by ring

theorem exists_nativeFirstDefectCommutatorWords_uniform_energy_bound
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
        ⟪nativeFirstDefectCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,F x⟫_ℝ| ≤
        C*eps * ∫ x : R3, referenceDensityFamily g1 L (lam,x) *
          finiteCoreSourceEnergy hO hD (actualReferenceBeta g1 L lam δ R p x) F x := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeFirstDefect_commutator_uniform_energy_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp
  rw [← nativeFirstDefect_commutator_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  exact hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 hb hH8 hsmall F hsupp

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
