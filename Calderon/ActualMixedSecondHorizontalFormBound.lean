import Calderon.ActualMixedSecondWordFormBound
import Calderon.ActualHorizontalNormBridge

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedSecondHorizontalFormBound
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ReferenceDensityBounds PrincipalCommutator ConformalDepth ReferenceWeightedApproximation
  ActualMixedDensityCoefficientJets ActualMixedDensityRemainderForm ActualMixedDensityRemainderProfile
  ActualMixedSecondWordFormBound ActualHorizontalNormBridge

/-- The complete retained actual mixed second word in the literal manuscript N,
with all L,p,R witnesses retained rather than replaced by an unrelated profile. -/
theorem exists_actual_mixedSecondRaw_horizontal_bound
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ R : ℝ, 0 < δ → 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eta : ℝ, 0 < eta → eta ≤ 1 → ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eta) →
      (∀ x ∈ K, MixedMetricFirstJetBound g1 g2 L lam x eps (referenceRadius δ R p L x)) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      |∫ x, mixedSecondRawDensity hF hO hD g1 g2 L lam G hG x| ≤
        C*eps*eta * referenceHorizontalNormSquare hO hD g1 L lam
          (actualReferenceBeta g1 L lam δ R p) G hG := by
  obtain ⟨M,hM,hgeom⟩ := exists_mixed_background_first_jet_bound g1 hg1 L K hK
  obtain ⟨CH,hCH,hComparison⟩ := exists_coordinate_horizontal_norm_comparison hO hD g1 hg1 L K hK
  let C : ℝ := 359640*M^3*CH
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ R hδ hR p hp eta heta heta1 g2 hg2 eps heps heps1 hb hs hh G hG hz
  have hr (x : R3) (hx : x ∈ K) : referenceRadius δ R p L x ≤ eta := by
    have hsq : 1 ≤ (actualReferenceBeta g1 L lam δ R p x)^2 := by nlinarith [hb x hx]
    have hrpos : 0 ≤ referenceRadius δ R p L x := (referenceRadius_pos δ R p L x hδ hR).le
    have hscale : referenceRadius δ R p L x ≤
        referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hrpos
    exact hscale.trans (hs x hx)
  have hrb (x : R3) (hx : x ∈ K) : referenceRadius δ R p L x*actualReferenceBeta g1 L lam δ R p x ≤ eta := by
    have hsq : actualReferenceBeta g1 L lam δ R p x ≤ (actualReferenceBeta g1 L lam δ R p x)^2 := by
      nlinarith [hb x hx]
    exact (mul_le_mul_of_nonneg_left hsq (referenceRadius_pos δ R p L x hδ hR).le).trans (hs x hx)
  have hsmall (x : R3) (hx : x ∈ K) : eps*referenceRadius δ R p L x ≤ 1 := by
    have hrpos : 0 ≤ referenceRadius δ R p L x := (referenceRadius_pos δ R p L x hδ hR).le
    have hscale : eps*referenceRadius δ R p L x ≤ referenceRadius δ R p L x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right heps1 hrpos
    exact hscale.trans ((hr x hx).trans heta1)
  have hWord := abs_integral_mixedSecondRawDensity_le_coordinate_norm hF hO hD g1 g2 hg1 hg2 L lam δ R p
    hL hδ hR hp K hK eps eta M heps heta.le hM (fun x hx => hgeom lam hlam x hx) hh hsmall hr hrb G hG hz
  have hComp : mixedCoordinateNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG ≤
      CH*referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG :=
    (hComparison lam hlam (actualReferenceBeta g1 L lam δ R p)
      (continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR)
      (fun x => actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x) hb G hG hz).1
  calc
    _ ≤ 359640*M^3*eps*eta*mixedCoordinateNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG := hWord
    _ ≤ 359640*M^3*eps*eta*(CH*referenceHorizontalNormSquare hO hD g1 L lam
        (actualReferenceBeta g1 L lam δ R p) G hG) := mul_le_mul_of_nonneg_left hComp (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Actual compact geometry and genuine fixed-L softplus witnesses provide the
same-witness horizontal allocation; only the actual h/r source jets remain hypotheses. -/
theorem exists_actual_mixedSecondRaw_horizontal_profile
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ R : ℝ, 0 < R ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ g2 : MatrixField, IsAdmissibleMetric g2 →
        ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
        (∀ x ∈ K, MixedMetricFirstJetBound g1 g2 L lam x eps (referenceRadius δ R p L x)) →
        ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
        (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
        |∫ x, mixedSecondRawDensity hF hO hD g1 g2 L lam G hG x| ≤
          C*eps*eta * referenceHorizontalNormSquare hO hD g1 L lam
            (actualReferenceBeta g1 L lam δ R p) G hG := by
  obtain ⟨C,hC,hBound⟩ := exists_actual_mixedSecondRaw_horizontal_bound hF hO hD g1 hg1 L hL K hK
  obtain ⟨p0,hp02,hProfile⟩ := exists_fixed_mixed_density_radius_profile g1 hg1 L hL K hK
  refine ⟨C,hC,p0,hp02,?_⟩
  intro p hp eta heta heta1
  obtain ⟨R,hR,hr⟩ := hProfile p hp eta heta heta1
  refine ⟨R,hR,?_⟩
  intro lam hlam δ hδ hδ1 g2 hg2 eps heps heps1 hh G hG hz
  have hp1 : 1 ≤ p := by omega
  exact hBound lam hlam δ R hδ hR p hp1 eta heta heta1 g2 hg2 eps heps heps1
    (fun x hx => (hr lam hlam δ hδ hδ1 x hx).1)
    (fun x hx => (hr lam hlam δ hδ hδ1 x hx).2.1) hh G hG hz

end OAI.AnisotropicCalderon.ActualMixedSecondHorizontalFormBound
