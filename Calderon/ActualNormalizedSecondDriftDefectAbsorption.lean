import Calderon.ActualNormalizedSecondDriftDefectBalancedBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectAbsorption
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

lemma sourceNormSquare_nonneg {ι : Type*} [Fintype ι]
    (g : MatrixField) (L lam : ℝ) (beta : R3 → ℝ) (hbeta : ∀ x, 0 ≤ beta x)
    (gradientZero : R3 → ι → SphereL2) (phiOne : R3 → SphereL2)
    (gradientHalf : R3 → ι → SphereL2) (phiThreeHalf : R3 → SphereL2) :
    0 ≤ sourceNormSquare g L lam beta gradientZero phiOne gradientHalf phiThreeHalf := by
  unfold sourceNormSquare
  apply integral_nonneg
  intro x
  exact sourceNormSquareIntegrand_nonneg (beta x) (hbeta x) _ _ _ _

lemma referenceHorizontalNormSquare_nonneg
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam : ℝ) (beta : R3 → ℝ) (hbeta : ∀ x, 0 ≤ beta x)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    0 ≤ referenceHorizontalNormSquare hO hD g L lam beta G hG := by
  unfold referenceHorizontalNormSquare
  exact sourceNormSquare_nonneg g L lam beta hbeta _ _ _ _

lemma abs_le_absorption_of_balanced_bound
    (z NG NV C eps tau : ℝ) (hNG : 0 ≤ NG) (hC : 0 < C)
    (heps : 0 ≤ eps) (htau : 0 < tau)
    (hbound : ∀ eta : ℝ, 0 < eta → |z| ≤ C*eps*(eta*NG+eta⁻¹*NV)) :
    |z| ≤ tau*NG+((C*eps)^2/tau)*NV := by
  by_cases hzero : eps=0
  · have ht := hbound 1 (by norm_num)
    simp only [hzero,mul_zero,zero_mul] at ht
    apply ht.trans
    simp only [hzero,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div,zero_mul,add_zero]
    exact mul_nonneg htau.le hNG
  · have hep : 0 < eps := lt_of_le_of_ne heps (Ne.symm hzero)
    have ht := hbound (tau/(C*eps)) (div_pos htau (mul_pos hC hep))
    convert ht using 1 <;> field_simp [ne_of_gt hC,ne_of_gt hep,ne_of_gt htau] <;> ring

theorem exists_normalizedSecondDriftDefect_coordinate_absorption_form_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ tau : ℝ, 0 < tau → ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      ∀ V : R3 × R3 → ℝ, ∀ hV : ContDiff ℝ ∞ V,
      (∀ x ∉ K, ∀ theta : UnitSphere, V (x,theta.val)=0) →
      |∫ x, referenceDensityFamily g1 L (lam,x)*
        ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ| ≤
        tau*sourceNormSquare g1 L lam (actualReferenceBeta g1 L lam δ R p)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
        (ambientBesselField hO hD 1 (by norm_num) G hG)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
        (ambientBesselField hO hD (3/2) (by norm_num) G hG) + ((C*eps)^2/tau)*sourceNormSquare g1 L lam (actualReferenceBeta g1 L lam δ R p)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
        (ambientBesselField hO hD 1 (by norm_num) V hV)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
        (ambientBesselField hO hD (3/2) (by norm_num) V hV) := by
  obtain ⟨C,hC,hbound⟩ := exists_normalizedSecondDriftDefect_coordinate_balanced_form_bound hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro tau htau lam hlam δ hδ hδ1 R hR p hp eps heps hb hsmall G hG hzG V hV hzV
  have hpos (x : R3) : 0 ≤ actualReferenceBeta g1 L lam δ R p x :=
    (actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x).le
  have hNG : 0 ≤ sourceNormSquare g1 L lam (actualReferenceBeta g1 L lam δ R p)
      (fun x j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG)
      (fun x j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG) :=
    sourceNormSquare_nonneg g1 L lam (actualReferenceBeta g1 L lam δ R p) hpos _ _ _ _
  apply abs_le_absorption_of_balanced_bound _ _ _ C eps tau hNG hC heps htau
  intro eta heta
  exact hbound lam hlam δ hδ hδ1 R hR p hp eps heps eta heta hb hsmall G hG hzG V hV hzV

theorem exists_normalizedSecondDriftDefect_horizontal_absorption_form_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ tau : ℝ, 0 < tau → ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps →
      (∀ x ∈ K, 1 ≤ actualReferenceBeta g1 L lam δ R p x) →
      (∀ x ∈ K, referenceRadius δ R p L x*(actualReferenceBeta g1 L lam δ R p x)^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) →
      ∀ V : R3 × R3 → ℝ, ∀ hV : ContDiff ℝ ∞ V,
      (∀ x ∉ K, ∀ theta : UnitSphere, V (x,theta.val)=0) →
      |∫ x, referenceDensityFamily g1 L (lam,x)*
        ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ| ≤
        tau*referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG +
          ((C*eps)^2/tau)*referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) V hV := by
  obtain ⟨C,hC,hbound⟩ := exists_normalizedSecondDriftDefect_horizontal_balanced_form_bound hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro tau htau lam hlam δ hδ hδ1 R hR p hp eps heps hb hsmall G hG hzG V hV hzV
  have hpos (x : R3) : 0 ≤ actualReferenceBeta g1 L lam δ R p x :=
    (actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x).le
  have hNG : 0 ≤ referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG :=
    referenceHorizontalNormSquare_nonneg hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) hpos G hG
  apply abs_le_absorption_of_balanced_bound _ _ _ C eps tau hNG hC heps htau
  intro eta heta
  exact hbound lam hlam δ hδ hδ1 R hR p hp eps heps eta heta hb hsmall G hG hzG V hV hzV

end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectAbsorption
