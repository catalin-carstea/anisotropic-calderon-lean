import Calderon.ActualFiniteHarmonicModelWeightedYAngularPart
import Calderon.ActualFiniteHarmonicModelWeightedFirstRotationJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualMixedDensityHigherCoefficientJets NormalizedPrincipalMetric CoordinateBootstrapJets
  ConformalDepth ReferenceWeightedApproximation PrincipalCommutator ReferenceDensityBounds

theorem exists_nativeWeightedYAngularPartMass_uniform_smallness
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*referenceRadius δ R p L x →
      referenceRadius δ R p L x*beta^2 ≤ eps →
      nativeWeightedYAngularPartMass g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ C*eps := by
  obtain ⟨J,hJ,hjets⟩ := exists_nativeWeightedFirst_degree_rotation_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M,hM,hbg⟩ := exists_mixed_background_coordinate_jet_bound g1 hg1 L K hK 2
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨120*M^2*J,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  let r := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := by linarith
  let mu := fun y : R3 => referenceDensityFamily g1 L (lam,y)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmw : HasCoordinateWordJetBound 2 mu x M beta 0 := by
    intro w hw
    have ht := (hbg lam hlam x hx).2.2.1 w hw
    change |coordinateFieldWordPartial w mu x| ≤ M at ht
    rw [Real.norm_eq_abs]
    exact ht.trans (le_mul_of_one_le_right hMpos.le (one_le_pow₀ hb))
  have hmi : |(mu x)⁻¹| ≤ M := by
    simpa only [coordinateFieldWordPartial] using (hbg lam hlam x hx).2.2.2 [] (by simp)
  have hd (j : Fin 3) : |directionalFDeriv (coordinateDirection j)
      (fun y => mu y*nativeReferenceWeightedFirstDegreeCoefficient g1 L lam δ R p h j y) x| ≤ 4*M*J*eps := by
    let d := nativeReferenceWeightedFirstDegreeCoefficient g1 L lam δ R p h j
    have hdS : ContDiff ℝ ∞ d := contDiff_nativeReferenceWeightedFirstDegreeCoefficient g1 hg1 L lam δ R p h hh hδ hR j
    have hdw : HasCoordinateWordJetBound 2 d x (J*r) beta 1 := by
      intro w hw
      simpa only [Real.norm_eq_abs] using
        (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall w hw j 0 0).1
    have ht := (hasCoordinateWordJetBound_mul 2 mu d hmu hdS x M (J*r) beta 0 1
      hMpos.le (mul_nonneg hJ.le hr.le) hb0 hmw hdw) [j] (by simp)
    have ht' : |directionalFDeriv (coordinateDirection j) (fun y => mu y*d y) x| ≤ (4*M*J)*(r*beta^2) := by
      convert ht using 1 <;> simp only [coordinateFieldWordPartial,Real.norm_eq_abs,List.length_cons,List.length_nil] <;> ring
    exact ht'.trans (mul_le_mul_of_nonneg_left hsmall (by positivity))
  have htau (j s t : Fin 3) : |directionalFDeriv (coordinateDirection j)
      (fun y => mu y*nativeReferenceWeightedFirstRotationCoefficient g1 L lam δ R p h j s t y) x| ≤ 4*M*J*eps := by
    let tau := nativeReferenceWeightedFirstRotationCoefficient g1 L lam δ R p h j s t
    have htS : ContDiff ℝ ∞ tau := contDiff_nativeReferenceWeightedFirstRotationCoefficient g1 hg1 L lam δ R p h hh hδ hR j s t
    have htw : HasCoordinateWordJetBound 2 tau x (J*r) beta 0 := by
      intro w hw
      simpa only [Real.norm_eq_abs,Nat.zero_add] using
        (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall w hw j s t).2
    have ht := (hasCoordinateWordJetBound_mul 2 mu tau hmu htS x M (J*r) beta 0 0
      hMpos.le (mul_nonneg hJ.le hr.le) hb0 hmw htw) [j] (by simp)
    have ht' : |directionalFDeriv (coordinateDirection j) (fun y => mu y*tau y) x| ≤ (4*M*J)*(r*beta) := by
      convert ht using 1 <;> simp only [coordinateFieldWordPartial,Real.norm_eq_abs,List.length_cons,List.length_nil] <;> ring
    have hrb : r*beta ≤ eps := (mul_le_mul_of_nonneg_left (by nlinarith : beta ≤ beta^2) hr.le).trans hsmall
    exact ht'.trans (mul_le_mul_of_nonneg_left hrb (by positivity))
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    add_le_add (hd j) (Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin 3))) =>
      Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin 3))) => htau j s t))))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  unfold nativeWeightedYAngularPartMass
  dsimp only
  have hsum0 : 0 ≤ (∑ j : Fin 3,
      (|directionalFDeriv (coordinateDirection j) (fun y => mu y*nativeReferenceWeightedFirstDegreeCoefficient g1 L lam δ R p h j y) x|+
      (∑ s : Fin 3, ∑ t : Fin 3, |directionalFDeriv (coordinateDirection j)
        (fun y => mu y*nativeReferenceWeightedFirstRotationCoefficient g1 L lam δ R p h j s t y) x|))) := by positivity
  have hm := mul_le_mul hmi hs hsum0 hMpos.le
  convert hm using 1 <;> ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
