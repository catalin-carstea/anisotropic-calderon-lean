import Calderon.ActualNormalizedSecondDriftDefectAbsorption
import Calderon.CommonProfileFamily

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftUniformAbsorption
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph BoundedAngularShift BoundedSpectralMultiplier SmoothSphereFields SmoothAngularApplication
  AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection ActualReferenceParallelRaising
  ActualReferenceModelTrace ActualReferenceOrdinaryPrincipal ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDQuadraticBound ActualReferenceDDHigherHCoframeJets
  ActualReferenceDDHigherGeometryJets
  ActualNormalizedSecondMetricDrift ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftWeightedCoefficients
  ActualNormalizedSecondDriftDefectWeightedJets ActualNormalizedSecondDriftDefectCoefficients
  ActualScalarPrincipalAdjoint ActualUnboundedFirstPrincipalFormBound ActualSupportLocalSecondForm
  ActualHorizontalNormBridge ReferenceDensityBounds PrincipalCommutator ConformalDepth RadiusProfile
  WeightedBaseSpectral SectionFiveErrorForms ReferenceWeightedApproximation
  ActualNormalizedSecondDriftDefectBilinearBound ActualNormalizedSecondDriftDefectBalancedBound
  ActualNormalizedSecondDriftDefectAbsorption

lemma actualReferenceBeta_eq_referenceProfileNorm
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) :
    actualReferenceBeta g L lam δ R p = referenceProfileNorm g lam δ R p L := by
  rfl

theorem exists_referenceProfile_actual_beta_threshold_radius
    (g : MatrixField) (hg : IsAdmissibleMetric g) (K : Set R3) (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ beta0 eps : ℝ, 0 < eps →
      ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          beta0 ≤ actualReferenceBeta g L lam δ R p x ∧
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ eps ∧
          referenceRadius δ R p L x*(actualReferenceBeta g L lam δ R p x)^2 ≤ eps := by
  obtain ⟨L,c0,c1,J1,J2,D,hL,hc0,hc1,hJ1,hJ2,hD,hbounds⟩ :=
    exists_referenceProfileBounds g hg K hK
  refine ⟨L,hL,?_⟩
  intro beta0 eps heps
  simpa only [actualReferenceBeta_eq_referenceProfileNorm] using
    referenceProfileBounds_choose_degree_radius g K L c0 c1 J1 J2 D hc0 hbounds beta0 eps heps

theorem exists_normalizedSecondDriftDefect_uniform_shrinking_absorption_form_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (K : Set R3) (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ eps : ℝ, 0 < eps →
      ∃ p : ℕ, 2 ≤ p ∧ ∃ R : ℝ, 0 < R ∧
        (∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x ∈ K,
          1 ≤ actualReferenceBeta g1 L lam δ R p x ∧
          ‖fderiv ℝ (referenceRadius δ R p L) x‖ ≤ eps ∧
          referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) ∧
        (∀ tau : ℝ, 0 < tau → ∀ lam ∈ Set.Icc (0 : ℝ) 1,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
          (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
          ∀ V : R3 × R3 → ℝ, ∀ hV : ContDiff ℝ ∞ V,
          (∀ x ∉ K, ∀ theta : UnitSphere, V (x,theta.val)=0) →
          |∫ x, referenceDensityFamily g1 L (lam,x)*
            ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ| ≤
            tau*referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG +
              (eps^2/tau)*referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) V hV) := by
  obtain ⟨L,hL,hchoose⟩ := exists_referenceProfile_actual_beta_threshold_radius g1 hg1 K hK
  obtain ⟨C,hC,hbound⟩ := exists_normalizedSecondDriftDefect_horizontal_absorption_form_bound
    hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨L,hL,?_⟩
  intro eps heps
  let e : ℝ := eps/(C+1)
  have hd : 0 < C+1 := by linarith
  have he : 0 < e := div_pos heps hd
  have hele : e ≤ eps := by
    dsimp [e]
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg heps.le hC.le]
  have hCe : C*e ≤ eps := by
    dsimp [e]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  obtain ⟨p,hp,R,hR,hprofile⟩ := hchoose 1 e he
  have hp1 : 1 ≤ p := by omega
  refine ⟨p,hp,R,hR,?_,?_⟩
  · intro lam hlam δ hδ hδ1 x hx
    obtain ⟨hb,hdr,hrb⟩ := hprofile lam hlam δ hδ hδ1 x hx
    exact ⟨hb,hdr.trans hele,hrb.trans hele⟩
  · intro tau htau lam hlam δ hδ hδ1 G hG hzG V hV hzV
    have hb := fun x hx => (hprofile lam hlam δ hδ hδ1 x hx).1
    have hsmall := fun x hx => (hprofile lam hlam δ hδ hδ1 x hx).2.2
    have ht := hbound tau htau lam hlam δ hδ hδ1 R hR p hp1 e he.le hb hsmall G hG hzG V hV hzV
    have hNV : 0 ≤ referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) V hV :=
      referenceHorizontalNormSquare_nonneg hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p)
        (fun x => (actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp1 x).le) V hV
    have hsquare : (C*e)^2 ≤ eps^2 := by
      nlinarith [mul_nonneg hC.le he.le]
    exact ht.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hsquare htau.le) hNV))

end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftUniformAbsorption
