import Calderon.ActualMixedDensityScalarZeroSmooth

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ReferenceDensityBounds PrincipalCommutator ActualPhysicalMixedFirst ActualHorizontalNormBridge
  ActualReferenceDDHigherGeometryJets CoordinateBootstrapJets ActualMixedDensityHigherCoefficientJets
  ActualMixedDensityRaisingCoefficientJets ActualMixedDensityRemainderForm ActualMixedDensityRemainderProfile
  AmbientAngularShift BoundedAngularShift SpectralWeightedGraph SpectralWeightComparison SectionFiveErrorForms
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ConformalDepth RadiusProfile ReferenceWeightedApproximation

theorem abs_integral_mixedDensityScalarZeroDensity_le_coordinate_norm
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hR : 0 < R) (hp : 1 ≤ p)
    (K : Set R3) (hK : IsCompact K) (eps eta M : ℝ)
    (heps : 0 ≤ eps) (heta : 0 ≤ eta) (hM : 1 ≤ M)
    (hgeom : ∀ x ∈ K, MixedPrincipalDensityBackgroundJetBound g1 L lam x M 3)
    (hH8 : ∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
      eps*referenceRadius δ R p L x)
    (hsmall : ∀ x ∈ K, eps*referenceRadius δ R p L x ≤ 1)
    (hb : ∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x)
    (hrad : ∀ x ∈ K, referenceRadius δ R p L x ≤ eta)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    |∫ x, mixedDensityScalarZeroDensity hF hO hD g1 g2 L lam δ R p G hG x| ≤
      497664*M^4*eps*eta^2 * mixedCoordinateNormSquare hO hD g1 L lam
        (actualReferenceBeta g1 L lam δ R p) G hG := by
  let beta : R3 → ℝ := actualReferenceBeta g1 L lam δ R p
  let NN : R3 → ℝ := mixedCoordinateNormSquareIntegrand hO hD beta G hG
  let F : R3 → ℝ := mixedDensityScalarZeroDensity hF hO hD g1 g2 L lam δ R p G hG
  have hBeta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hPos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hmu : ContDiff ℝ ∞ (fun x : R3 => referenceDensityFamily g1 L (lam,x)) :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hField : ContDiff ℝ ∞ (mixedDensityScalarZeroField hF hO hD g1 g2 L lam δ R p G hG) :=
    contDiff_mixedDensityScalarZeroField hF hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR G hG
  have hCont : Continuous F := (hmu.mul (hField.inner ℝ (contDiff_ambientSphereL2 G hG))).continuous
  have hzero (x : R3) (hx : x ∉ K) : F x=0 := by
    dsimp only [F,mixedDensityScalarZeroDensity]
    rw [ambientSphereL2_eq_zero G hG x (hz x hx),inner_zero_right,mul_zero]
  have hSupp : HasCompactSupport F := HasCompactSupport.intro hK hzero
  have hi : Integrable F := hCont.integrable_of_hasCompactSupport hSupp
  have hN : Integrable (fun x => referenceDensityFamily g1 L (lam,x)*NN x) :=
    OAI.AnisotropicCalderon.ActualSupportLocalSecondForm.integrable_ambient_source_norm_on_compact
      hO hD g1 hg1 L lam beta hBeta hPos G hG K hK hz
  have hPoint (x : R3) : |F x| ≤ (497664*M^4*eps*eta^2)*
      (referenceDensityFamily g1 L (lam,x)*NN x) := by
    have hMu := referenceDensityFamily_pos g1 hg1 L (lam,x)
    have hNN : 0 ≤ NN x := sourceNormSquareIntegrand_nonneg (beta x) (hPos x).le _ _ _ _
    by_cases hx : x ∈ K
    · have h : |F x| ≤ (497664*M^4*eps*(referenceRadius δ R p L x)^2)*
          (referenceDensityFamily g1 L (lam,x)*NN x) :=
        abs_mixedDensityScalarZeroDensity_le_coordinate_integrand hF hO hD g1 g2 hg1 hg2 L lam δ R p x
          eps M beta hδ hR heps hM (hsmall x hx) (hb x hx) (hgeom x hx) (hH8 x hx) G hG
      have hs : (referenceRadius δ R p L x)^2 ≤ eta^2 := by
        nlinarith only [referenceRadius_pos δ R p L x hδ hR,hrad x hx]
      have hCoefficient : 497664*M^4*eps*(referenceRadius δ R p L x)^2 ≤
          497664*M^4*eps*eta^2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      have hWeighted : (497664*M^4*eps*(referenceRadius δ R p L x)^2)*
          (referenceDensityFamily g1 L (lam,x)*NN x) ≤
          (497664*M^4*eps*eta^2)*(referenceDensityFamily g1 L (lam,x)*NN x) :=
        mul_le_mul_of_nonneg_right hCoefficient (mul_nonneg hMu.le hNN)
      exact h.trans hWeighted
    · rw [hzero x hx]
      simp only [abs_zero]
      exact mul_nonneg (by positivity) (mul_nonneg hMu.le hNN)
  have hNid : mixedCoordinateNormSquare hO hD g1 L lam beta G hG =
      ∫ x, referenceDensityFamily g1 L (lam,x)*NN x := by
    unfold mixedCoordinateNormSquare NN mixedCoordinateNormSquareIntegrand
    exact sourceNormSquare_eq_density_integral g1 hg1 L lam _ _ _ _ _
  change |∫ x, F x| ≤ 497664*M^4*eps*eta^2*mixedCoordinateNormSquare hO hD g1 L lam beta G hG
  rw [hNid]
  exact OAI.AnisotropicCalderon.ScalarHilbertFormBounds.abs_integral_le_const_mul_integral
    (X := R3) (volume : Measure R3) F (fun x => referenceDensityFamily g1 L (lam,x)*NN x)
    (497664*M^4*eps*eta^2) hi hN hPoint

end OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
