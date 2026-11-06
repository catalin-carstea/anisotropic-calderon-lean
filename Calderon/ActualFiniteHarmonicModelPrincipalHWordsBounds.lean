import Calderon.ActualFiniteHarmonicModelFirstAngularBounds
import Calderon.ActualFiniteHarmonicCoreLeibniz

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  ActualNormalizedPrincipalDensityCoefficientJets ActualReferenceDDHigherGeometryJets
  ActualMixedDensityScalarZeroForm CoordinateBootstrapJets PrincipalCommutator ConformalDepth
  SmoothSphereFields SmoothAngularApplication ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev principalHWordFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] principalHWordFunction
lemma nativePrincipalCoefficient_apply_eq_actualPrincipal
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (i k : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k F x =
      actualPrincipalMatrix g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) x i k • F x := by
  change (referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i k) • F x = _
  rw [actualPrincipalMatrix_normalized_eq]
  rfl


lemma coefficientDerivative_nativePrincipalCoefficient_apply
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (i k : Fin 3)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k) F x =
      directionalFDeriv v (fun y => actualPrincipalMatrix g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) y i k) x • F x := by
  unfold nativePrincipalCoefficient
  rw [coefficientDerivative_coreScalar]
  change directionalFDeriv v (fun y => referenceRadius δ R p L y *
    referenceNormalizedPrincipalMatrix g1 g2 L lam y i k) x • F x = _
  have he : (fun y => actualPrincipalMatrix g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) y i k) =
      fun y => referenceRadius δ R p L y * referenceNormalizedPrincipalMatrix g1 g2 L lam y i k := by
    funext y
    rw [actualPrincipalMatrix_normalized_eq]
    rfl
  rw [he]


theorem exists_nativePrincipal_H_coefficient_word_smallness
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
      ∀ i k l : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖(nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l *
        coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
          (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k)) F x‖ ≤
          (C * eps / beta) * ‖coreWeightOperator hO hD (besselWeight 1) F x‖ ∧
      ‖(nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k *
        coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
          (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)) F x‖ ≤
          (C * eps / beta) * ‖coreWeightOperator hO hD (besselWeight 1) F x‖ ∧
      ‖(nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k *
        coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
          (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
            (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l))) F x‖ ≤
          (C * eps) * ‖coreWeightOperator hO hD (besselWeight 1) F x‖ := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 1
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 1
  obtain ⟨CH,hCH,hH⟩ := exists_nativeHFirstAngularCoefficient_uniform_coordinate_word_bounds
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  let Cp : ℝ := normalizedPrincipalCoordinateJetConstant 1*Cr*M
  let C : ℝ := 1+Cp*CH
  have hCp : 0 < Cp := by dsimp only [Cp,normalizedPrincipalCoordinateJetConstant]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hEnlarge : Cp*CH ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k l F
  let r : ℝ := referenceRadius δ R p L x
  let A : R3 → ℝ := fun y => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) y i k
  let HN : R3 → SphereL2 →L[ℝ] SphereL2 :=
    nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p l
  let n : ℝ := ‖coreWeightOperator hO hD (besselWeight 1) F x‖
  have hn : 0 ≤ n := norm_nonneg _
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  change r*beta^2 ≤ eps at hsmall
  have hr1 : r ≤ 1 :=
    ((le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans hsmall).trans heps1
  have hsm1 : eps*referenceRadius δ R p L x ≤ 1 := by change eps*r ≤ 1; nlinarith
  have hrb : r*beta ≤ eps/beta := (le_div_iff₀ hbpos).2 (by nlinarith)
  have hj (w : List (Fin 3)) (hw : w.length ≤ 1) :
      |coordinateFieldWordPartial w A x| ≤ Cp*r*beta^w.length := by
    exact abs_actualNormalizedPrincipal_coordinate_word_le g1 g2 hg1 hg2 L lam δ R p x
      eps M Cr 1 (by norm_num) hδ hR heps hM hCr.le hsm1 hb
      (hgeom lam hlam x hx) (hRadius lam hlam δ hδ hδ1 R hR p hp x hx) hH8 w hw i k
  have hq : |A x| ≤ Cp*r := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using hj [] (by simp)
  have hdq : |directionalFDeriv (coordinateDirection l) A x| ≤ Cp*r*beta := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,pow_one] using
      hj [l] (by simp)
  have hH0 : ‖HN x‖ ≤ CH := by
    simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one] using
      hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l [] (by simp)
  have hH1 : ‖directionalFDeriv (coordinateDirection i) HN x‖ ≤ CH*beta := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd,pow_one] using
      hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l [i] (by simp)
  have hH2 : ‖directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection k) HN) x‖ ≤ CH*beta^2 := by
    simpa only [coordinateFieldWordPartial,List.length_cons,List.length_nil,Nat.reduceAdd] using
      hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l [i,k] (by simp)
  have hfirstScale : Cp*CH*(r*beta) ≤ C*eps/beta := by
    calc
      _ ≤ Cp*CH*(eps/beta) := mul_le_mul_of_nonneg_left hrb (mul_nonneg hCp.le hCH.le)
      _ ≤ C*(eps/beta) := mul_le_mul_of_nonneg_right hEnlarge (div_nonneg heps hb0)
      _ = _ := by ring
  have hsecondScale : Cp*CH*(r*beta^2) ≤ C*eps := by
    exact (mul_le_mul_of_nonneg_left hsmall (mul_nonneg hCp.le hCH.le)).trans
      (mul_le_mul_of_nonneg_right hEnlarge heps)
  have hHF : ‖nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l F x‖ ≤ CH*n := by
    rw [nativeH_firstAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p l hg2 hδ hR F x]
    exact ((HN x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hH0 hn)
  have hc := OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm.contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
    g1 g2 hg1 hg2 L lam δ R p hδ hR i k
  have hPrincipalDerivative : coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
      (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k) =
      coreScalar hO hD
        (directionalFDeriv (coordinateDirection l) (fun y => referenceRadius δ R p L y *
          referenceNormalizedPrincipalMatrix g1 g2 L lam y i k))
        (contDiff_directionalFDeriv (coordinateDirection l) _ hc) := by
    unfold nativePrincipalCoefficient
    exact coefficientDerivative_coreScalar hO hD _ _ _
  have hcomm : Commute (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
      (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
        (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k)) := by
    rw [hPrincipalDerivative]
    exact nativeH_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l _ _
  have hcommF := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) hcomm.eq
  refine ⟨?_,?_,?_⟩
  · rw [hcommF,Module.End.mul_apply,coefficientDerivative_nativePrincipalCoefficient_apply,
      norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (Cp*r*beta)*(CH*n) := mul_le_mul hdq hHF (norm_nonneg _) (by positivity)
      _ = (Cp*CH*(r*beta))*n := by ring
      _ ≤ (C*eps/beta)*n := mul_le_mul_of_nonneg_right hfirstScale hn
  · rw [Module.End.mul_apply,nativePrincipalCoefficient_apply_eq_actualPrincipal,
      coefficientDerivative_nativeH_firstAngular_apply,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (Cp*r)*((CH*beta)*n) := mul_le_mul hq
        (((directionalFDeriv (coordinateDirection i) HN x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hH1 hn)) (norm_nonneg _) (by positivity)
      _ = (Cp*CH*(r*beta))*n := by ring
      _ ≤ (C*eps/beta)*n := mul_le_mul_of_nonneg_right hfirstScale hn
  · rw [Module.End.mul_apply,nativePrincipalCoefficient_apply_eq_actualPrincipal,
      coefficientDerivative_second_nativeH_firstAngular_apply,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (Cp*r)*((CH*beta^2)*n) := mul_le_mul hq
        (((directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) HN) x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hH2 hn)) (norm_nonneg _) (by positivity)
      _ = (Cp*CH*(r*beta^2))*n := by ring
      _ ≤ (C*eps)*n := mul_le_mul_of_nonneg_right hsecondScale hn

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
