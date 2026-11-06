import Calderon.ActualFiniteHarmonicModelPrincipalZWordScalarAction
import Calderon.ActualNormalizedPrincipalDensityCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric ReferenceDensityBounds PrincipalCommutator
  ActualMixedDensityScalarZeroForm
  ActualNormalizedPrincipalDensityCoefficientJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherLogFrameJets AmbientReferenceRaising
  CoordinateBootstrapJets ReferenceWeightedApproximation ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

theorem exists_nativePrincipalDefectWordScalar_uniform_smallness
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i j a k l : Fin 3,
      |nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [k] x| ≤ C*eps ∧
      |nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [k,l] x| ≤ C*eps*beta := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 0
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 0
  obtain ⟨CZ,hCZ,hZ⟩ := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds
    g1 hg1 L hL K hK 2
  let Cp : ℝ := normalizedPrincipalCoordinateJetConstant 0*Cr*M
  let C : ℝ := 1+Cp*CZ
  have hCp : 0 < Cp := by dsimp only [Cp,normalizedPrincipalCoordinateJetConstant]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hEnlarge : Cp*CZ ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i j a k l
  let r : ℝ := referenceRadius δ R p L x
  let A : R3 → ℝ := fun y => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) y i j
  let f : R3 → ℝ := referenceFrameDerivative g1 L lam a
    (fun y => Real.log (referenceRadius δ R p L y))
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hb0 : 0 ≤ beta := hbpos.le
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 :=
    ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans hsmall).trans heps1
  have hsm1 : eps*referenceRadius δ R p L x ≤ 1 := by
    change eps*r ≤ 1
    nlinarith
  have hq : |A x| ≤ Cp*r := by
    have ht := abs_actualNormalizedPrincipal_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x
      eps M Cr 0 (by norm_num) hδ hR heps hM hCr.le hsm1 hb
      (hgeom lam hlam x hx) (hRadius lam hlam δ hδ hδ1 R hR p hp x hx) hH8
      [] (by simp) i j
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one,A,Cp,r,beta] using ht
  have hf1 : |coordinateFieldWordPartial [k] f x| ≤ CZ*beta^2 := by
    simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,f,beta,actualReferenceBeta] using
      (hZ lam hlam δ hδ hδ1 R hR p hp x hx hb [k] (by simp)).1 a
  have hf2 : |coordinateFieldWordPartial [k,l] f x| ≤ CZ*beta^3 := by
    simpa only [List.length_cons,List.length_nil,Nat.reduceAdd,f,beta,actualReferenceBeta] using
      (hZ lam hlam δ hδ hδ1 R hR p hp x hx hb [k,l] (by simp)).1 a
  constructor
  · change |A x * coordinateFieldWordPartial [k] f x| ≤ _
    rw [abs_mul]
    calc
      _ ≤ (Cp*r)*(CZ*beta^2) := mul_le_mul hq hf1 (abs_nonneg _) (by positivity)
      _ = Cp*CZ*(r*beta^2) := by ring
      _ ≤ Cp*CZ*eps := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ C*eps := mul_le_mul_of_nonneg_right hEnlarge heps
  · change |A x * coordinateFieldWordPartial [k,l] f x| ≤ _
    rw [abs_mul]
    calc
      _ ≤ (Cp*r)*(CZ*beta^3) := mul_le_mul hq hf2 (abs_nonneg _) (by positivity)
      _ = (Cp*CZ)*(r*beta^2)*beta := by ring
      _ ≤ (Cp*CZ)*eps*beta := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsmall (by positivity)) hb0
      _ ≤ C*eps*beta := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hEnlarge heps) hb0

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
