import Calderon.ActualMixedDensityScalarZeroIntegral

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

theorem exists_actual_mixedDensityScalarZero_horizontal_bound_of_H8
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ R : ℝ, 0 < δ → 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 → ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eta) →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps*referenceRadius δ R p L x) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      |∫ x, mixedDensityScalarZeroDensity hF hO hD g1 g2 L lam δ R p G hG x| ≤
        C*eps*eta^2 * referenceHorizontalNormSquare hO hD g1 L lam
          (actualReferenceBeta g1 L lam δ R p) G hG := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_principal_density_background_jet_bound g1 hg1 L K hK 3
  obtain ⟨CH,hCH,hComparison⟩ := exists_coordinate_horizontal_norm_comparison hO hD g1 hg1 L K hK
  let C : ℝ := 497664*M^4*CH
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ R hδ hR p hp eta heta heta1 g2 hg2 eps heps heps1 hb hs hH8 G hG hz
  have hr (x : R3) (hx : x ∈ K) : referenceRadius δ R p L x ≤ eta := by
    have hsq : 1 ≤ (actualReferenceBeta g1 L lam δ R p x)^2 := by nlinarith [hb x hx]
    have hRadiusScale : referenceRadius δ R p L x ≤
        referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hsq (referenceRadius_pos δ R p L x hδ hR).le
    exact hRadiusScale.trans (hs x hx)
  have hsmall (x : R3) (hx : x ∈ K) : eps*referenceRadius δ R p L x ≤ 1 := by
    have hEpsScale : eps*referenceRadius δ R p L x ≤ referenceRadius δ R p L x := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right heps1 (referenceRadius_pos δ R p L x hδ hR).le
    exact hEpsScale.trans ((hr x hx).trans heta1)
  have hWord := abs_integral_mixedDensityScalarZeroDensity_le_coordinate_norm hF hO hD g1 g2 hg1 hg2 L lam δ R p
    hL hδ hR hp K hK eps eta M heps heta.le hM (fun x hx => hgeom lam hlam x hx)
    hH8 hsmall hb hr G hG hz
  have hComp : mixedCoordinateNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG ≤
      CH*referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG :=
    (hComparison lam hlam (actualReferenceBeta g1 L lam δ R p)
      (continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR)
      (fun x => actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x) hb G hG hz).1
  calc
    _ ≤ 497664*M^4*eps*eta^2*mixedCoordinateNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG := hWord
    _ ≤ 497664*M^4*eps*eta^2*(CH*referenceHorizontalNormSquare hO hD g1 L lam
        (actualReferenceBeta g1 L lam δ R p) G hG) := mul_le_mul_of_nonneg_left hComp (by positivity)
    _ = _ := by dsimp [C]; ring

theorem exists_actual_mixedDensityScalarZero_horizontal_profile_of_H8
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
        (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
          eps*referenceRadius δ R p L x) →
        ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
        (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
        |∫ x, mixedDensityScalarZeroDensity hF hO hD g1 g2 L lam δ R p G hG x| ≤
          C*eps*eta^2 * referenceHorizontalNormSquare hO hD g1 L lam
            (actualReferenceBeta g1 L lam δ R p) G hG := by
  obtain ⟨C,hC,hBound⟩ := exists_actual_mixedDensityScalarZero_horizontal_bound_of_H8 hF hO hD g1 hg1 L hL K hK
  obtain ⟨p0,hp02,hProfile⟩ := exists_fixed_mixed_density_radius_profile g1 hg1 L hL K hK
  refine ⟨C,hC,p0,hp02,?_⟩
  intro p hp eta heta heta1
  obtain ⟨R,hR,hr⟩ := hProfile p hp eta heta heta1
  refine ⟨R,hR,?_⟩
  intro lam hlam δ hδ hδ1 g2 hg2 eps heps heps1 hH8 G hG hz
  have hp1 : 1 ≤ p := by omega
  exact hBound lam hlam δ R hδ hR p hp1 eta heta heta1 g2 hg2 eps heps heps1
    (fun x hx => (hr lam hlam δ hδ hδ1 x hx).1)
    (fun x hx => (hr lam hlam δ hδ hδ1 x hx).2.1) hH8 G hG hz

end OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
