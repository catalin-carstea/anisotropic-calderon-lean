import Calderon.ActualFiniteHarmonicModelVFirstBalancedAngularJets
import Calderon.ActualFiniteHarmonicModelFirstAngularCoefficientJets
import Calderon.ActualFiniteHarmonicModelFirstAngularBounds
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
private abbrev vFirstBalancedBoundFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] vFirstBalancedBoundFunction
lemma nativeVFirstBalancedAngularCoefficient_eq_normalized_add_shift_correction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) :
    nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j =
      fun x => nativeVFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j x +
        ∑ a : Fin 3, (-physicalMixedFirstCoefficient g1 L lam
            (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x) •
          ((balancedDerivative hF hO hD a + balancedRaising hF hO hD a) -
            (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a)) := by
  funext x
  unfold nativeVFirstBalancedAngularCoefficient nativeVFirstAngularCoefficient
  simp only [Fin.sum_univ_three]
  module


theorem exists_nativeVFirstBalancedAngularCoefficient_uniform_coordinate_word_bounds
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
        (nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x‖ ≤
          (C*eps/beta) * beta^w.length := by
  obtain ⟨CV,hCV,hV⟩ := exists_modelDefectFirstNormalizedCoefficient_uniform_coordinate_word_smallness hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨J,hJ,hjets⟩ := exists_native_first_angular_coefficients_uniform_coordinate_word_bounds g1 g2 hg1 hg2 L hL K hK
  let T (a : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
    (balancedDerivative hF hO hD a+balancedRaising hF hO hD a)-
      (normalizedDerivative hF hO hD a+normalizedRaising hF hO hD a)
  let MT : ℝ := 1+∑ a : Fin 3, ‖T a‖
  let C : ℝ := 1+CV+12*J*MT
  have hMT : 1 ≤ MT := by
    have ht := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => norm_nonneg (T a))
    dsimp only [MT]
    linarith
  have hMT0 : 0 ≤ MT := le_trans zero_le_one hMT
  have hT (a : Fin 3) : ‖T a‖ ≤ MT := by
    have ht := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) => norm_nonneg (T b)) (Finset.mem_univ a)
    dsimp only [MT]
    linarith
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j w hw
  let r := referenceRadius δ R p L x
  let rate := eps/beta
  let m (a : Fin 3) := physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j
  let c (a : Fin 3) (y : R3) := -m a y
  let VN := nativeVFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j
  let Corr (y : R3) := ∑ a : Fin 3, c a y • T a
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  have hrate : 0 ≤ rate := div_nonneg heps hb0
  change r*beta^2 ≤ eps at hsmall
  have hrb : r*beta ≤ rate := (le_div_iff₀ hbpos).2 (by nlinarith)
  have her : eps*r ≤ rate := (mul_le_of_le_one_left hr.le heps1).trans
    ((le_mul_of_one_le_right hr.le hb).trans hrb)
  have hmS (a : Fin 3) : ContDiff ℝ ∞ (m a) := contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
    (fun s t => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam s t) a j
  have hcS (a : Fin 3) : ContDiff ℝ ∞ (c a) := (hmS a).neg
  have hmj (a : Fin 3) : HasCoordinateWordJetBound 2 (m a) x (J*rate) beta 0 := by
    intro v hv
    have ht := (hjets lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall v hv j a 0 0).1
    have ht' : ‖coordinateFieldWordPartial v (m a) x‖ ≤ (J*eps*r)*beta^v.length := by
      simpa only [m,Real.norm_eq_abs,mul_assoc] using ht
    have hscale : J*eps*r ≤ J*rate := by nlinarith [mul_le_mul_of_nonneg_left her hJ.le]
    have hs := mul_le_mul_of_nonneg_right hscale (pow_nonneg hb0 v.length)
    exact ht'.trans (by simpa only [Nat.zero_add] using hs)
  have hcj (a : Fin 3) : HasCoordinateWordJetBound 2 (c a) x (J*rate) beta 0 :=
    hasCoordinateWordJetBound_neg 2 (m a) (hmS a) x (J*rate) beta 0 (hmj a)
  have hTerm (a : Fin 3) : HasCoordinateWordJetBound 2 (fun y => c a y • T a) x (4*J*MT*rate) beta 0 := by
    have hTj := hasCoordinateWordJetBound_const_normed 2 (T a) x MT beta (hT a) hb0
    have ht := hasCoordinateWordJetBound_smul 2 (c a) (fun _ : R3 => T a) (hcS a) contDiff_const
      x (J*rate) MT beta 0 0 (mul_nonneg hJ.le hrate) hMT0 hb0 (hcj a) hTj
    convert ht using 1 <;> simp only [show (2:ℝ)^2=4 by norm_num,Nat.zero_add] <;> ring
  have hCorrS : ContDiff ℝ ∞ Corr := ContDiff.sum (fun a _ => (hcS a).smul contDiff_const)
  have hCorrj : HasCoordinateWordJetBound 2 Corr x (12*J*MT*rate) beta 0 := by
    have ht := hasCoordinateWordJetBound_sum 2 (fun a y => c a y • T a)
      (fun a => (hcS a).smul contDiff_const) x (4*J*MT*rate) beta 0 hTerm
    convert ht using 1 <;> simp only [Fintype.card_fin,Nat.cast_ofNat] <;> ring
  have hVj : HasCoordinateWordJetBound 2 VN x (CV*rate) beta 0 := by
    intro v hv
    unfold VN
    rw [nativeVFirstAngularCoefficient_eq_normalized_defect]
    simpa only [rate,Nat.zero_add,mul_div_assoc] using
      hV lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j v hv
  have hj := hasCoordinateWordJetBound_add 2 VN Corr
    (contDiff_nativeVFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)
    hCorrS x (CV*rate) (12*J*MT*rate) beta 0 hVj hCorrj
  have he : (fun y => VN y+Corr y) = nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j := by
    funext y
    exact (congrFun (nativeVFirstBalancedAngularCoefficient_eq_normalized_add_shift_correction hO hD hF g1 g2 hg1 L lam δ R p j) y).symm
  rw [he] at hj
  calc
    _ ≤ (CV*rate+12*J*MT*rate)*beta^w.length := by simpa only [Nat.zero_add] using hj w hw
    _ ≤ (C*rate)*beta^w.length := mul_le_mul_of_nonneg_right (by dsimp only [C]; nlinarith) (pow_nonneg hb0 _)
    _ = _ := by dsimp only [rate]; ring

theorem exists_nativeV_uniform_half_angular_forms
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
      |⟪nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x,G x⟫_ℝ| ≤
        (C*eps/beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) F x,G x⟫_ℝ| ≤
        (C * eps) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ ∧
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
          (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)) F x,G x⟫_ℝ| ≤
        (C * eps * beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x‖ := by
  obtain ⟨C,hC,hBounds⟩ := exists_nativeVFirstBalancedAngularCoefficient_uniform_coordinate_word_bounds
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j i k F G
  let HB := nativeVFirstBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j
  let U := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x
  let V := coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  have hbpos : 0 < beta := by linarith
  have hfirst : (C*eps/beta)*beta=C*eps := div_mul_cancel₀ _ hbpos.ne'
  have hsecond : (C*eps/beta)*beta^2=C*eps*beta := by rw [pow_two,← mul_assoc,hfirst]
  have h0 : ‖HB x‖ ≤ C*eps/beta := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [] (by simp)
  have h1 : ‖directionalFDeriv (coordinateDirection i) HB x‖ ≤ C*eps := by
    have hs := hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [i] (by simp)
    simp only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd,pow_one] at hs
    change ‖directionalFDeriv (coordinateDirection i) HB x‖ ≤ (C*eps/beta)*beta at hs
    simpa only [hfirst] using hs
  have h2 : ‖directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection k) HB) x‖ ≤ C*eps*beta := by
    have hs := hBounds lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j [i,k] (by simp)
    simp only [coordinateFieldWordPartial,List.length_nil,List.length_cons,Nat.reduceAdd] at hs
    change ‖directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) HB) x‖ ≤ (C*eps/beta)*beta^2 at hs
    simpa only [hsecond] using hs
  have hform (A : SphereL2 →L[ℝ] SphereL2) (B : ℝ) (hA : ‖A‖ ≤ B) :
      |⟪A U,V⟫_ℝ| ≤ B*‖U‖*‖V‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        ((A.le_opNorm U).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg U))) (norm_nonneg V))
  refine ⟨?_,?_,?_⟩
  · rw [nativeV_firstAngular_inner_half hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F G x]
    exact hform (HB x) (C*eps/beta) h0
  · rw [coefficientDerivative_nativeV_firstAngular_inner_half hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR i F G x]
    exact hform (directionalFDeriv (coordinateDirection i) HB x) (C*eps) h1
  · rw [coefficientDerivative_second_nativeV_firstAngular_inner_half hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR i k F G x]
    exact hform (directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) HB) x) (C*eps*beta) h2

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
