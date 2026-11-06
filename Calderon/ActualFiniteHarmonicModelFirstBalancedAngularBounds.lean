import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularJets
import Calderon.ActualMixedDensityHigherCoefficientJets

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  BalancedAngularShift ActualModelCommutatorWords ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualPhysicalMixedFirst ActualMixedDensityHigherCoefficientJets
  ActualMixedDensityScalarZeroForm CoordinateBootstrapJets
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  SmoothMetricFrame SmoothSphereFields SmoothAngularApplication PrincipalCommutator
  ConformalDepth ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev firstBalancedBoundFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] firstBalancedBoundFunction
lemma nativeHFirstBalancedAngularCoefficient_eq_normalized_add_shift_correction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) :
    nativeHFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j =
      fun x => nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j x +
        ∑ a : Fin 3, (-2 * referenceMetricGramFrame g1 L (lam,x) a j -
          physicalMixedFirstCoefficient g1 L lam
            (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x) •
          ((balancedDerivative hF hO hD a + balancedRaising hF hO hD a) -
            (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a)) := by
  funext x
  unfold nativeHFirstBalancedAngularCoefficient nativeHFirstAngularCoefficient
  simp only [Fin.sum_univ_three]
  module


theorem exists_nativeHFirstBalancedAngularCoefficient_uniform_coordinate_word_bounds
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j : Fin 3, ∀ w : List (Fin 3), w.length ≤ 2 →
      ‖coordinateFieldWordPartial w
        (nativeHFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x‖ ≤
          C * beta^w.length := by
  obtain ⟨CH,hCH,hH⟩ := exists_nativeHFirstAngularCoefficient_uniform_coordinate_word_bounds
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 2
  let T (a : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
    (balancedDerivative hF hO hD a + balancedRaising hF hO hD a) -
      (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a)
  let MT : ℝ := 1+∑ a : Fin 3, ‖T a‖
  let C : ℝ := 1+CH+384*M*MT
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hMT : 1 ≤ MT := by
    have hh : 0 ≤ ∑ a : Fin 3, ‖T a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [MT]
    linarith
  have hMT0 : 0 ≤ MT := le_trans zero_le_one hMT
  have hT (a : Fin 3) : ‖T a‖ ≤ MT := by
    have hh : ‖T a‖ ≤ ∑ b : Fin 3, ‖T b‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    dsimp only [MT]
    linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j w hw
  let r : ℝ := referenceRadius δ R p L x
  let E (a : Fin 3) : R3 → ℝ := fun y => referenceMetricGramFrame g1 L (lam,y) a j
  let m (a : Fin 3) : R3 → ℝ := physicalMixedFirstCoefficient g1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam) a j
  let c (a : Fin 3) : R3 → ℝ := fun y => (-2 : ℝ)*E a y-m a y
  let Corr : R3 → SphereL2 →L[ℝ] SphereL2 := fun y => ∑ a : Fin 3, c a y • T a
  let HN := nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hb2 : 1 ≤ beta^2 := one_le_pow₀ hb
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 := ((le_mul_of_one_le_right hr.le hb2).trans hsmall).trans heps1
  have hsm1 : eps*r ≤ 1 := by nlinarith
  have hES (a : Fin 3) : ContDiff ℝ ∞ (E a) :=
    (contDiff_piLp_apply (p := 2) (i := j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a)
  have hh := ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference
    g1 g2 hg1 hg2 L lam
  have hmS (a : Fin 3) : ContDiff ℝ ∞ (m a) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  have hcS (a : Fin 3) : ContDiff ℝ ∞ (c a) :=
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (-2 : ℝ))).mul (hES a)).sub (hmS a)
  have hEj (a : Fin 3) : HasCoordinateWordJetBound 2 (E a) x M beta 0 := by
    intro v hv
    have ht := (hgeom lam hlam x hx).1.1 v hv a j
    calc
      ‖coordinateFieldWordPartial v (E a) x‖ = |coordinateFieldWordPartial v (E a) x| := Real.norm_eq_abs _
      _ ≤ M := ht
      _ ≤ M*beta^(0+v.length) := by
        simpa only [Nat.zero_add,mul_one] using
          mul_le_mul_of_nonneg_left (one_le_pow₀ hb) hM0
  have hmj (a : Fin 3) : HasCoordinateWordJetBound 2 (m a) x (24*M) beta 0 := by
    intro v hv
    have ht := abs_physicalMixedFirstCoefficient_coordinate_word_le g1 g2 hg1 hg2
      L lam x eps r M 2 (by norm_num) heps hr.le hM0 (hgeom lam hlam x hx).1 hH8 v hv a j
    have ht' : |coordinateFieldWordPartial v (m a) x| ≤ 24*M*(eps*r) := by
      convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num] <;> ring
    calc
      ‖coordinateFieldWordPartial v (m a) x‖ = |coordinateFieldWordPartial v (m a) x| := Real.norm_eq_abs _
      _ ≤ 24*M*(eps*r) := ht'
      _ ≤ 24*M := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hsm1 (by positivity : 0 ≤ 24*M)
      _ ≤ (24*M)*beta^(0+v.length) := by
        simpa only [Nat.zero_add,mul_one] using
          mul_le_mul_of_nonneg_left (one_le_pow₀ hb) (by positivity : 0 ≤ 24*M)
  have hMinusTwo : HasCoordinateWordJetBound 2 (fun _ : R3 => (-2 : ℝ)) x 2 beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (-2 : ℝ) x 2 beta (by norm_num) hb0
  have hcj (a : Fin 3) : HasCoordinateWordJetBound 2 (c a) x (32*M) beta 0 := by
    have ht := hasCoordinateWordJetBound_mul 2 (fun _ : R3 => (-2 : ℝ)) (E a)
      contDiff_const (hES a) x 2 M beta 0 0 (by norm_num) hM0 hb0 hMinusTwo (hEj a)
    have ht' : HasCoordinateWordJetBound 2 (fun y => (-2 : ℝ)*E a y) x (8*M) beta 0 := by
      convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
    have hs := hasCoordinateWordJetBound_sub 2 (fun y => (-2 : ℝ)*E a y) (m a)
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (-2 : ℝ))).mul (hES a))
      (hmS a) x (8*M) (24*M) beta 0 ht' (hmj a)
    convert hs using 1 <;> ring
  have hTj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun _ : R3 => T a) x MT beta 0 :=
    hasCoordinateWordJetBound_const_normed 2 (T a) x MT beta (hT a) hb0
  have hTermj (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => c a y • T a) x
      (128*M*MT) beta 0 := by
    have ht := hasCoordinateWordJetBound_smul 2 (c a) (fun _ : R3 => T a)
      (hcS a) contDiff_const x (32*M) MT beta 0 0 (by positivity) hMT0 hb0 (hcj a) (hTj a)
    convert ht using 1 <;> simp only [show (2 : ℝ)^2=4 by norm_num,Nat.add_zero] <;> ring
  have hCorrS : ContDiff ℝ ∞ Corr := ContDiff.sum (fun a _ => (hcS a).smul contDiff_const)
  have hCorrj := hasCoordinateWordJetBound_sum 2 (fun a y => c a y • T a)
    (fun a => (hcS a).smul contDiff_const) x (128*M*MT) beta 0 hTermj
  have hCorrj' : HasCoordinateWordJetBound 2 Corr x (384*M*MT) beta 0 := by
    convert hCorrj using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hHN : HasCoordinateWordJetBound 2 HN x CH beta 0 := by
    intro v hv
    simpa only [Nat.zero_add] using
      hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j v hv
  have hj := hasCoordinateWordJetBound_add 2 HN Corr
    (contDiff_nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)
    hCorrS x CH (384*M*MT) beta 0 hHN hCorrj'
  change HasCoordinateWordJetBound 2 (fun y =>
    nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j y +
      ∑ a : Fin 3, (-2*referenceMetricGramFrame g1 L (lam,y) a j -
        physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j y) •
        ((balancedDerivative hF hO hD a + balancedRaising hF hO hD a) -
          (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a))) x
      (CH+384*M*MT) beta 0 at hj
  rw [← nativeHFirstBalancedAngularCoefficient_eq_normalized_add_shift_correction hO hD hF g1 g2 hg1 L lam δ R p j] at hj
  have hEnlarge : CH+384*M*MT ≤ C := by dsimp only [C]; linarith
  exact (hj w hw).trans (by simpa only [Nat.zero_add] using
    mul_le_mul_of_nonneg_right hEnlarge (pow_nonneg hb0 w.length))


theorem exists_nativeH_uniform_half_angular_forms
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j i k : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x,G x⟫_ℝ| ≤
        C * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) F x,G x⟫_ℝ| ≤
        (C * beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
          (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j)) F x,G x⟫_ℝ| ≤
        (C * beta^2) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_nativeHFirstBalancedAngularCoefficient_uniform_coordinate_word_bounds
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j i k F G
  let HB := nativeHFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j
  let U := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let V := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  have h0 : ‖HB x‖ ≤ C := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [] (by simp)
  have h1 : ‖directionalFDeriv (coordinateDirection i) HB x‖ ≤ C*beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd,pow_one] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [i] (by simp)
  have h2 : ‖directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection k) HB) x‖ ≤ C*beta^2 := by
    simpa only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [i,k] (by simp)
  have hform (A : SphereL2 →L[ℝ] SphereL2) (B : ℝ) (hA : ‖A‖ ≤ B) :
      |⟪A U,V⟫_ℝ| ≤ B*‖U‖*‖V‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        ((A.le_opNorm U).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg U))) (norm_nonneg V))
  refine ⟨?_,?_,?_⟩
  · rw [nativeH_firstAngular_inner_half hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F G x]
    exact hform (HB x) C h0
  · rw [coefficientDerivative_nativeH_firstAngular_inner_half hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR i F G x]
    exact hform (directionalFDeriv (coordinateDirection i) HB x) (C*beta) h1
  · rw [coefficientDerivative_second_nativeH_firstAngular_inner_half hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR i k F G x]
    exact hform (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) HB) x) (C*beta^2) h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
