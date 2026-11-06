import Calderon.ActualNormalizedSecondDriftDefectCoefficients
import Calderon.ActualReferenceDDQuadraticBound

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectBilinearBound
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

/- Actual independently defined b2 adjoint defect: uniform bilinear component bound.
   Full E/F/U/H and the density/coercivity/rigidity argument remain separate. -/

lemma contDiff_normalizedSecondWeightedDriftAdjointDefect
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG) := by
  unfold normalizedSecondWeightedDriftAdjointDefect
  exact (contDiff_normalizedSecondWeightedDriftAdjointField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR).sub
    (contDiff_normalizedSecondWeightedDriftField hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR)

lemma integrable_normalizedSecondWeightedDriftAdjointDefect_density_pair
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (V : R3 × R3 → ℝ) (hV : ContDiff ℝ ∞ V)
    (K : Set R3) (hK : IsCompact K)
    (hzV : ∀ x ∉ K, ∀ theta : UnitSphere, V (x,theta.val)=0) :
    Integrable (fun x => referenceDensityFamily g1 L (lam,x)*
      ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ) := by
  exact integrable_density_pair_of_contDiff g1 hg1 L lam _ _
    (contDiff_normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR G hG)
    (contDiff_ambientSphereL2 V hV) (hasCompactSupport_ambientSphereL2 V hV K hK hzV)

theorem normalizedSecondWeightedDriftAdjointDefect_inner_half_identity
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (V : R3 × R3 → ℝ) (hV : ContDiff ℝ ∞ V) (x : R3) :
    ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ =
      (∑ j : Fin 3, ⟪normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
        (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
        ambientBesselField hO hD (1/2) (by norm_num) V hV x⟫_ℝ) +
      ⟪normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x
        (ambientBesselField hO hD (3/2) (by norm_num) G hG x),
        ambientBesselField hO hD (1/2) (by norm_num) V hV x⟫_ℝ := by
  rw [normalizedSecondWeightedDriftAdjointDefect_normalized_representation hO hD g1 g2 L lam δ R p hg1 hg2 hδ hR G hG x,
    inner_add_left,sum_inner]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    have hbetween := directional_ambientBesselField_between_graph hO hD 1 (1/2)
      (by norm_num) (by norm_num) G hG x (coordinateDirection j)
    have houtput := preservesSphereSpectralGraphs_normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
      (besselWeight (-(1/2))) _ _ (by convert hbetween using 1 <;> norm_num [sphereBesselGraph])
    exact inner_besselGraph_inverse_pair hO hD (1/2) _ _ _ _ houtput
      (ambientBesselField_graph hO hD (1/2) (by norm_num) V hV x)
  · have hbetween := ambientBesselField_between_graph hO hD 2 (3/2)
      (by norm_num) (by norm_num) G hG x
    have houtput := preservesSphereSpectralGraphs_normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x
      (besselWeight (-(1/2))) _ _ (by convert hbetween using 1 <;> norm_num [sphereBesselGraph])
    exact inner_besselGraph_inverse_pair hO hD (1/2) _ _ _ _ houtput
      (ambientBesselField_graph hO hD (1/2) (by norm_num) V hV x)

lemma abs_inner_first_half_pair_le_two_source_integrands
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta C eps : ℝ) (hb : 1 ≤ beta) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (A : SphereL2 →L[ℝ] SphereL2) (hA : ‖A‖ ≤ C*eps/beta)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (V : R3 × R3 → ℝ) (hV : ContDiff ℝ ∞ V) (x : R3) (j : Fin 3) :
    |⟪A (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
      ambientBesselField hO hD (1/2) (by norm_num) V hV x⟫_ℝ| ≤
      C*eps*(sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x) + sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x)) := by
  let NG := sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x)
  let NV := sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x)
  let a := ‖directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x‖
  let b := ‖ambientBesselField hO hD 1 (by norm_num) V hV x‖
  let c := ‖ambientBesselField hO hD (1/2) (by norm_num) V hV x‖
  have hp : 0 < beta := by linarith
  have hCE : 0 ≤ C*eps := mul_nonneg hC heps
  have hcoef : 0 ≤ C*eps/beta := div_nonneg hCE hp.le
  have hhalf : c ≤ b := norm_bessel_half_le_one hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2) (by norm_num) V hV x)
    (ambientBesselField_graph hO hD 1 (by norm_num) V hV x)
  have hgrad : beta⁻¹*a^2 ≤ NG := by
    have hs := norm_sq_le_sum (fun k => directionalFDeriv (coordinateDirection k)
      (ambientBesselField hO hD (1/2) (by norm_num) G hG) x) j
    have ht := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hp.le)
    have hg0 : 0 ≤ ∑ k : Fin 3, ‖directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x‖^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hg1 : 0 ≤ beta^2*‖ambientBesselField hO hD 1 (by norm_num) G hG x‖^2 := mul_nonneg (sq_nonneg beta) (sq_nonneg _)
    have hg3 : 0 ≤ beta*‖ambientBesselField hO hD (3/2) (by norm_num) G hG x‖^2 := mul_nonneg hp.le (sq_nonneg _)
    dsimp [NG,sourceNormSquareIntegrand,a]
    linarith
  have hvalue : beta^2*b^2 ≤ NV := by
    have hv0 : 0 ≤ ∑ k : Fin 3, ‖directionalFDeriv (coordinateDirection k) (ambientSphereL2 V hV) x‖^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hvh : 0 ≤ beta⁻¹*(∑ k : Fin 3, ‖directionalFDeriv (coordinateDirection k)
      (ambientBesselField hO hD (1/2) (by norm_num) V hV) x‖^2) :=
      mul_nonneg (inv_nonneg.mpr hp.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hv3 : 0 ≤ beta*‖ambientBesselField hO hD (3/2) (by norm_num) V hV x‖^2 := mul_nonneg hp.le (sq_nonneg _)
    dsimp [NV,sourceNormSquareIntegrand,b]
    linarith
  have hn := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hA (norm_nonneg (directionalFDeriv (coordinateDirection j)
      (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)))
      (norm_nonneg (ambientBesselField hO hD (1/2) (by norm_num) V hV x))
  have ht := mul_le_mul_of_nonneg_right (A.le_opNorm (directionalFDeriv (coordinateDirection j)
    (ambientBesselField hO hD (1/2) (by norm_num) G hG) x))
      (norm_nonneg (ambientBesselField hO hD (1/2) (by norm_num) V hV x))
  calc
    _ ≤ (C*eps/beta*a)*c := (abs_real_inner_le_norm _ _).trans (ht.trans hn)
    _ ≤ (C*eps/beta*a)*b := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hcoef (norm_nonneg _))
    _ = (C*eps)*((a*b)/beta) := by ring
    _ ≤ (C*eps)*(beta⁻¹*a^2+beta^2*b^2) :=
      mul_le_mul_of_nonneg_left (norm_product_div_le_source_weights beta a b hb) hCE
    _ ≤ C*eps*(NG+NV) := mul_le_mul_of_nonneg_left (add_le_add hgrad hvalue) hCE

lemma abs_inner_zero_half_pair_le_two_source_integrands
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (beta C eps : ℝ) (hb : 1 ≤ beta) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (A : SphereL2 →L[ℝ] SphereL2) (hA : ‖A‖ ≤ C*eps)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (V : R3 × R3 → ℝ) (hV : ContDiff ℝ ∞ V) (x : R3) :
    |⟪A (ambientBesselField hO hD (3/2) (by norm_num) G hG x),
      ambientBesselField hO hD (1/2) (by norm_num) V hV x⟫_ℝ| ≤
      C*eps*(sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x) + sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x)) := by
  let NG := sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x)
  let NV := sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x)
  let a := ‖ambientBesselField hO hD (3/2) (by norm_num) G hG x‖
  let b := ‖ambientBesselField hO hD (1/2) (by norm_num) V hV x‖
  have hp : 0 < beta := by linarith
  have hCE : 0 ≤ C*eps := mul_nonneg hC heps
  have hhalf : ‖ambientBesselField hO hD (1/2) (by norm_num) V hV x‖ ≤
      ‖ambientBesselField hO hD 1 (by norm_num) V hV x‖ := norm_bessel_half_le_one hO hD _ _ _
    (ambientBesselField_graph hO hD (1/2) (by norm_num) V hV x)
    (ambientBesselField_graph hO hD 1 (by norm_num) V hV x)
  have hGweights : beta*a^2 ≤ NG := by
    have hg0 : 0 ≤ ∑ k : Fin 3, ‖directionalFDeriv (coordinateDirection k) (ambientSphereL2 G hG) x‖^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hg1 : 0 ≤ beta^2*‖ambientBesselField hO hD 1 (by norm_num) G hG x‖^2 := mul_nonneg (sq_nonneg beta) (sq_nonneg _)
    have hgh : 0 ≤ beta⁻¹*(∑ k : Fin 3, ‖directionalFDeriv (coordinateDirection k)
      (ambientBesselField hO hD (1/2) (by norm_num) G hG) x‖^2) :=
      mul_nonneg (inv_nonneg.mpr hp.le) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    dsimp [NG,sourceNormSquareIntegrand,a]
    linarith
  have hVweights : beta⁻¹*b^2 ≤ NV := by
    have ht := lower_angular_weights_le_sourceNormSquareIntegrand beta hb
      (fun k => directionalFDeriv (coordinateDirection k) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD (1/2) (by norm_num) V hV x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun k => directionalFDeriv (coordinateDirection k) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x) hhalf
    have hn : 0 ≤ beta*‖ambientBesselField hO hD (3/2) (by norm_num) V hV x‖^2 := mul_nonneg hp.le (sq_nonneg _)
    dsimp [NV,b] at *
    linarith
  calc
    _ ≤ ‖A (ambientBesselField hO hD (3/2) (by norm_num) G hG x)‖*b := abs_real_inner_le_norm _ _
    _ ≤ (‖A‖*a)*b := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    _ ≤ (C*eps*a)*b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (norm_nonneg _)
    _ = (C*eps)*(b*a) := by ring
    _ ≤ (C*eps)*(beta⁻¹*b^2+beta*a^2) := mul_le_mul_of_nonneg_left (mul_le_weighted_sq beta b a hp) hCE
    _ ≤ C*eps*(NG+NV) := mul_le_mul_of_nonneg_left ((add_le_add hVweights hGweights).trans_eq (by ring)) hCE

theorem exists_normalizedSecondDriftDefect_pointwise_bilinear_coordinate_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      ∀ eps : ℝ, 0 ≤ eps →
      ∀ x ∈ K, let beta := actualReferenceBeta g1 L lam δ R p x;
      1 ≤ beta → referenceRadius δ R p L x*beta^2 ≤ eps →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      ∀ V : R3 × R3 → ℝ, ∀ hV : ContDiff ℝ ∞ V,
      |⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ| ≤
        C*eps*(sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x) + sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x)) := by
  obtain ⟨C,hC,hcoeff⟩ := exists_normalizedSecondDriftDefectNormalized_uniform_coordinate_word_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK 0
  refine ⟨4*C,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps x hx beta hb hsmall G hG V hV
  have hraw := hcoeff lam hlam δ hδ hδ1 R hR p hp eps heps x hx hb hsmall [] (by simp)
  have hpB : 0 < beta := by linarith
  have hCE : 0 ≤ C*eps := mul_nonneg hC.le heps
  have hfirst (j : Fin 3) : ‖normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x‖ ≤ C*eps/beta := by
    have ht : ‖normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x‖ ≤ C*eps/beta^2 := by
      simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one,beta,actualReferenceBeta] using hraw.1 j
    apply ht.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hpB) hpB).mpr
    exact mul_le_mul_of_nonneg_left (show beta ≤ beta^2 by nlinarith) hCE
  have hzero : ‖normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x‖ ≤ C*eps := by
    have ht : ‖normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x‖ ≤ C*eps/beta := by
      simpa only [coordinateFieldWordPartial,List.length_nil,pow_zero,mul_one,beta,actualReferenceBeta] using hraw.2
    apply ht.trans
    apply (div_le_iff₀ hpB).mpr
    nlinarith [mul_nonneg hCE (sub_nonneg.mpr hb)]
  have hterms (j : Fin 3) := abs_inner_first_half_pair_le_two_source_integrands hO hD beta C eps hb hC.le heps
    (normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x) (hfirst j) G hG V hV x j
  have hz := abs_inner_zero_half_pair_le_two_source_integrands hO hD beta C eps hb hC.le heps
    (normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x) hzero G hG V hV x
  rw [normalizedSecondWeightedDriftAdjointDefect_inner_half_identity hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR G hG V hV x]
  have hs := abs_sum_three_le (fun j => ⟪normalizedSecondDriftDefectFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
    (directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x),
    ambientBesselField hO hD (1/2) (by norm_num) V hV x⟫_ℝ) (C*eps*(sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x) + sourceNormSquareIntegrand beta
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x))) hterms
  exact (abs_add_le _ _).trans ((add_le_add hs hz).trans_eq (by ring))

theorem exists_normalizedSecondDriftDefect_coordinate_bilinear_form_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
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
        C*eps*(sourceNormSquare g1 L lam (actualReferenceBeta g1 L lam δ R p)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
        (ambientBesselField hO hD 1 (by norm_num) G hG)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
        (ambientBesselField hO hD (3/2) (by norm_num) G hG) + sourceNormSquare g1 L lam (actualReferenceBeta g1 L lam δ R p)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
        (ambientBesselField hO hD 1 (by norm_num) V hV)
        (fun x j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
        (ambientBesselField hO hD (3/2) (by norm_num) V hV)) := by
  obtain ⟨C,hC,hpoint⟩ := exists_normalizedSecondDriftDefect_pointwise_bilinear_coordinate_bound hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps hb hsmall G hG hzG V hV hzV
  let beta := actualReferenceBeta g1 L lam δ R p
  let NG : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG) x)
      (ambientBesselField hO hD 1 (by norm_num) G hG x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) G hG) x)
      (ambientBesselField hO hD (3/2) (by norm_num) G hG x)
  let NV : R3 → ℝ := fun x => sourceNormSquareIntegrand (beta x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientSphereL2 V hV) x)
      (ambientBesselField hO hD 1 (by norm_num) V hV x)
      (fun j => directionalFDeriv (coordinateDirection j) (ambientBesselField hO hD (1/2) (by norm_num) V hV) x)
      (ambientBesselField hO hD (3/2) (by norm_num) V hV x)
  let FF : R3 → ℝ := fun x => referenceDensityFamily g1 L (lam,x)*
    ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ
  have hpos (x : R3) : 0 < beta x := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp x
  have hcont : Continuous beta := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hi : Integrable FF := integrable_normalizedSecondWeightedDriftAdjointDefect_density_pair hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR G hG V hV K hK hzV
  have hNG : Integrable (fun x => referenceDensityFamily g1 L (lam,x)*NG x) :=
    integrable_ambient_source_norm_on_compact hO hD g1 hg1 L lam beta hcont hpos G hG K hK hzG
  have hNV : Integrable (fun x => referenceDensityFamily g1 L (lam,x)*NV x) :=
    integrable_ambient_source_norm_on_compact hO hD g1 hg1 L lam beta hcont hpos V hV K hK hzV
  have hsum : (fun x => referenceDensityFamily g1 L (lam,x)*(NG x+NV x)) =
      (fun x => referenceDensityFamily g1 L (lam,x)*NG x+referenceDensityFamily g1 L (lam,x)*NV x) := by funext x; ring
  have hN : Integrable (fun x => referenceDensityFamily g1 L (lam,x)*(NG x+NV x)) := by rw [hsum];exact hNG.add hNV
  have hbound (x : R3) : |FF x| ≤ (C*eps)*(referenceDensityFamily g1 L (lam,x)*(NG x+NV x)) := by
    by_cases hx : x ∈ K
    · have ht := hpoint lam hlam δ hδ hδ1 R hR p hp eps heps x hx (hb x hx) (hsmall x hx) G hG V hV
      change |referenceDensityFamily g1 L (lam,x)*
        ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ| ≤ _
      rw [abs_mul,abs_of_pos (referenceDensityFamily_pos g1 hg1 L (lam,x))]
      calc
        _ ≤ referenceDensityFamily g1 L (lam,x)*(C*eps*(NG x+NV x)) :=
          mul_le_mul_of_nonneg_left ht (referenceDensityFamily_pos g1 hg1 L (lam,x)).le
        _ = _ := by ring
    · have hzphi := ambientSphereL2_eq_zero V hV x (hzV x hx)
      have hg0 : 0 ≤ NG x := sourceNormSquareIntegrand_nonneg (beta x) (hpos x).le _ _ _ _
      have hv0 : 0 ≤ NV x := sourceNormSquareIntegrand_nonneg (beta x) (hpos x).le _ _ _ _
      have hrho : 0 ≤ referenceDensityFamily g1 L (lam,x) := (referenceDensityFamily_pos g1 hg1 L (lam,x)).le
      change |referenceDensityFamily g1 L (lam,x)*
        ⟪normalizedSecondWeightedDriftAdjointDefect hO hD g1 g2 hg1 L lam δ R p G hG x,ambientSphereL2 V hV x⟫_ℝ| ≤ _
      rw [hzphi,inner_zero_right,mul_zero,abs_zero]
      positivity
  have hiabs : Integrable (fun x => |FF x|) := by simpa only [Real.norm_eq_abs] using hi.norm
  have hint : |∫ x, FF x| ≤ (C*eps)*(∫ x, referenceDensityFamily g1 L (lam,x)*(NG x+NV x)) := by
    calc
      _ ≤ ∫ x, |FF x| := abs_integral_le_integral_abs
      _ ≤ ∫ x, (C*eps)*(referenceDensityFamily g1 L (lam,x)*(NG x+NV x)) := integral_mono hiabs (hN.const_mul _) hbound
      _ = _ := integral_const_mul _ _
  rw [hsum,integral_add hNG hNV] at hint
  simp_rw [sourceNormSquare_eq_density_integral g1 hg1 L lam]
  exact hint

theorem exists_normalizedSecondDriftDefect_horizontal_bilinear_form_bound
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
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
        C*eps*(referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) G hG +
          referenceHorizontalNormSquare hO hD g1 L lam (actualReferenceBeta g1 L lam δ R p) V hV) := by
  obtain ⟨C,hC,hbound⟩ := exists_normalizedSecondDriftDefect_coordinate_bilinear_form_bound hO hD g1 g2 hg1 hg2 L hL K hK
  obtain ⟨Ch,hCh,hcompare⟩ := exists_coordinate_horizontal_norm_comparison hO hD g1 hg1 L K hK
  refine ⟨C*Ch,mul_pos hC hCh,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps hb hsmall G hG hzG V hV hzV
  have ht := hbound lam hlam δ hδ hδ1 R hR p hp eps heps hb hsmall G hG hzG V hV hzV
  have hcont := continuous_actualReferenceBeta g1 hg1 L lam δ R p hL hδ hR
  have hpos := actualReferenceBeta_pos g1 hg1 L lam δ R p hL hδ hR hp
  have hNG := hcompare lam hlam (actualReferenceBeta g1 L lam δ R p) hcont hpos hb G hG hzG
  have hNV := hcompare lam hlam (actualReferenceBeta g1 L lam δ R p) hcont hpos hb V hV hzV
  have hm := mul_le_mul_of_nonneg_left (add_le_add hNG.1 hNV.1) (mul_nonneg hC.le heps)
  exact ht.trans (hm.trans_eq (by ring))

end OAI.AnisotropicCalderon.ActualNormalizedSecondDriftDefectBilinearBound
