import Calderon.ActualFiniteHarmonicModelHAngularPart
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ReferenceWeightedApproximation
  CoordinateBootstrapJets ConformalDepth ActualHorizontalNormBridge ActualReferenceDDHigherGeometryJets

theorem exists_nativeHAngularPartMass_uniform_bound
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*referenceRadius δ R p L x →
      referenceRadius δ R p L x*beta^2 ≤ eps → ∀ j : Fin 3,
      nativeHAngularPartMass g1 g2 L lam δ R p j x ≤ C := by
  obtain ⟨J,hJ,hjets⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  refine ⟨20*J,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j
  let r := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  change r*beta^2 ≤ eps at hsmall
  have hrb : r*beta ≤ 1 := by
    have ht : r*beta ≤ r*beta^2 := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hb)]
    exact ht.trans (hsmall.trans heps1)
  have hr1 : r ≤ 1 := (le_mul_of_one_le_right hr.le hb).trans hrb
  have her : eps*r ≤ 1 := (mul_le_mul heps1 hr1 hr.le (by norm_num)).trans (by norm_num)
  have hd0 : |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x| ≤ J*r*beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one] using
      (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp) j 0 0 0).2.2.1
  have hd : |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x| ≤ J :=
    hd0.trans (by nlinarith [mul_le_mul_of_nonneg_left hrb hJ.le])
  have hf (a : Fin 3) : |referenceMetricGramFrame g1 L (lam,x) a j| ≤ J := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp) j a 0 0).2.2.2.2.2
  have hm (a : Fin 3) : |physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤ J := by
    have ht := (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp) j a 0 0).1
    have ht' : |physicalMixedFirstCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤ J*eps*r := by
      simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using ht
    exact ht'.trans (by nlinarith [mul_le_mul_of_nonneg_left her hJ.le])
  have hfs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => hf a)
  have hms := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => mul_le_mul_of_nonneg_left (hm a) (by norm_num : (0 : ℝ) ≤ 2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hfs hms
  unfold nativeHAngularPartMass
  nlinarith

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
