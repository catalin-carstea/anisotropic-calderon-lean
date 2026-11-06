import Calderon.ActualFiniteHarmonicModelPrincipalHWordsBounds
import Calderon.ActualFiniteHarmonicModelH0ReversedForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ActualScalarPrincipalAdjoint ReferenceDensityBounds
  ActualNormalizedPrincipalDensityCoefficientJets ActualReferenceDDHigherGeometryJets
  ActualMixedDensityScalarZeroForm CoordinateBootstrapJets PrincipalCommutator ConformalDepth
  SmoothSphereFields SmoothAngularApplication NormalizedPrincipalMetric
  NormalizedPrincipalMetricSmooth ReferenceWeightedApproximation
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev principalH0ReversedWordFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] principalH0ReversedWordFunction
theorem exists_nativePrincipal_H0_uniform_half_threehalf_forms
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
      ∀ i k l m : Fin 3, ∀ F G : smoothCompactFiniteSphereCore hO hD,
      |⟪((nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) *
        coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
          (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k)) F x,G x⟫_ℝ| ≤
          (C * eps) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
            ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ ∧
      |⟪(nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k *
        coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
          ((nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))) F x,G x⟫_ℝ| ≤
          (C * eps) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
            ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ ∧
      |⟪(nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k *
        coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
          (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection m))
            ((nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)))) F x,G x⟫_ℝ| ≤
          (C * eps * beta) * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
            ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 1
  obtain ⟨Cr,hCr,hRadius⟩ := exists_actual_radius_coordinate_jet_bound g1 hg1 L hL K hK 1
  obtain ⟨CH,hCH,hH⟩ := exists_nativeH0_uniform_half_threehalf_forms
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  let Cp : ℝ := normalizedPrincipalCoordinateJetConstant 1*Cr*M
  let C : ℝ := 1+Cp*CH
  have hCp : 0 < Cp := by dsimp only [Cp,normalizedPrincipalCoordinateJetConstant]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hEnlarge : Cp*CH ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k l m F G
  let r : ℝ := referenceRadius δ R p L x
  let A : R3 → ℝ := fun y => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) y i k
  let n : ℝ := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
    ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖
  have hn : 0 ≤ n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
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
  obtain ⟨hh0,hh1,hh2⟩ := hH lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
    hb hH8 hsmall l m F G
  have hH0 : |⟪(nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,G x⟫_ℝ| ≤ (CH*beta)*n := by
    simpa only [mul_assoc] using hh0
  have hH1 : |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
    ((nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,G x⟫_ℝ| ≤ (CH*beta^2)*n := by
    simpa only [mul_assoc] using hh1
  have hH2 : |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
    (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection m))
      ((nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))) F x,G x⟫_ℝ| ≤ (CH*beta^3)*n := by
    simpa only [mul_assoc] using hh2
  have hfirstScale : Cp*CH*(r*beta^2) ≤ C*eps := by
    exact (mul_le_mul_of_nonneg_left hsmall (mul_nonneg hCp.le hCH.le)).trans
      (mul_le_mul_of_nonneg_right hEnlarge heps)
  have hsecondScale : Cp*CH*(r*beta^3) ≤ C*eps*beta := by
    calc
      _ = (Cp*CH*(r*beta^2))*beta := by ring
      _ ≤ (C*eps)*beta := mul_le_mul_of_nonneg_right hfirstScale hb0
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
  have hcomm : Commute ((nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
      (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection l))
        (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k)) := by
    rw [hPrincipalDerivative]
    exact nativeH0_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR _ _
  have hcommF := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) hcomm.eq
  refine ⟨?_,?_,?_⟩
  · rw [hcommF,Module.End.mul_apply,coefficientDerivative_nativePrincipalCoefficient_apply,
      real_inner_smul_left,abs_mul]
    calc
      _ ≤ (Cp*r*beta)*((CH*beta)*n) := mul_le_mul hdq hH0 (abs_nonneg _) (by positivity)
      _ = (Cp*CH*(r*beta^2))*n := by ring
      _ ≤ (C*eps)*n := mul_le_mul_of_nonneg_right hfirstScale hn
      _ = _ := by dsimp only [n]; ring
  · rw [Module.End.mul_apply,nativePrincipalCoefficient_apply_eq_actualPrincipal,
      real_inner_smul_left,abs_mul]
    calc
      _ ≤ (Cp*r)*((CH*beta^2)*n) := mul_le_mul hq hH1 (abs_nonneg _) (by positivity)
      _ = (Cp*CH*(r*beta^2))*n := by ring
      _ ≤ (C*eps)*n := mul_le_mul_of_nonneg_right hfirstScale hn
      _ = _ := by dsimp only [n]; ring
  · rw [Module.End.mul_apply,nativePrincipalCoefficient_apply_eq_actualPrincipal,
      real_inner_smul_left,abs_mul]
    calc
      _ ≤ (Cp*r)*((CH*beta^3)*n) := mul_le_mul hq hH2 (abs_nonneg _) (by positivity)
      _ = (Cp*CH*(r*beta^3))*n := by ring
      _ ≤ (C*eps*beta)*n := mul_le_mul_of_nonneg_right hsecondScale hn
      _ = _ := by dsimp only [n]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
