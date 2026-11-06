import Calderon.ActualFiniteHarmonicModelVAngularPart
import Calderon.ActualFiniteHarmonicModelReferenceExpansionCoefficientBounds
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  ActualPhysicalMixedFirst NormalizedPrincipalMetric ReferenceWeightedApproximation
  CoordinateBootstrapJets ConformalDepth ActualHorizontalNormBridge
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativeVAngularPartMass_uniform_smallness
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤ eps*referenceRadius δ R p L x →
      referenceRadius δ R p L x*beta^2 ≤ eps → ∀ j : Fin 3,
      nativeVAngularPartMass g1 g2 L lam δ R p j x ≤ C*eps/beta := by
  obtain ⟨J,hJ,hjets⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  refine ⟨8*J,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j
  let r := referenceRadius δ R p L x
  let rate := eps/beta
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := by linarith
  have hrate : 0 ≤ rate := div_nonneg heps hbpos.le
  change r*beta^2 ≤ eps at hsmall
  have hrb : r*beta ≤ rate := (le_div_iff₀ hbpos).2 (by nlinarith)
  have hrr : r ≤ rate := (le_mul_of_one_le_right hr.le hb).trans hrb
  have her : eps*r ≤ rate := (by nlinarith [mul_nonneg (sub_nonneg.mpr heps1) hr.le] : eps*r ≤ r).trans hrr
  have hd0 : |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x| ≤ J*r*beta := by
    simpa only [ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial,List.length_nil,Nat.add_zero,pow_one] using
      (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp) j 0 0 0).2.2.1
  have hd : |nativeFirstDegreeCoefficient g1 g2 L lam δ R p j x| ≤ J*rate :=
    hd0.trans (by nlinarith [mul_le_mul_of_nonneg_left hrb hJ.le])
  have hm (a : Fin 3) : |physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤ J*rate := by
    have ht := (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall [] (by simp) j a 0 0).1
    have ht' : |physicalMixedFirstCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x| ≤ J*eps*r := by
      simpa only [ActualReferenceDDHigherGeometryJets.coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using ht
    exact ht'.trans (by nlinarith [mul_le_mul_of_nonneg_left her hJ.le])
  have hms := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => mul_le_mul_of_nonneg_left (hm a) (by norm_num : (0 : ℝ) ≤ 2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hms
  unfold nativeVAngularPartMass
  calc
    _ ≤ 2*(J*rate)+3*(2*(J*rate)) := add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num)) hms
    _ = _ := by dsimp only [rate]; ring

theorem exists_nativeVAngularPart_uniform_linear_expansion
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
        (nativeVAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) x (C*eps/beta) := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeVAngularPartMass_uniform_smallness hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j
  exact hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
    (hasCoreScalarExpansionBound_nativeVAngularPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j x)
    (hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
