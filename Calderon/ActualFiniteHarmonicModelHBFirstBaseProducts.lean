import Calderon.ActualFiniteHarmonicModelHHalfNorm
import Calderon.ActualFiniteHarmonicModelBAngularAdjointHalfNorm
import Calderon.ActualFiniteHarmonicModelFirstBalancedBounds
import Calderon.ActualFiniteHarmonicModelFirstBalancedAngularBounds

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
  ConformalDepth ReferenceWeightedApproximation ActualReferenceDDSpectralTransport
  ActualReferenceDDNormalizedCoefficient ActualScalarPrincipalAdjoint
  ActualNormalizedSecondMetricDrift
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev hbFirstProductsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] hbFirstProductsFunction
theorem exists_nativeHB_first_base_uniform_half_threehalf_forms
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
      ∀ l i j : Fin 3, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      let H := nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l
      let B := nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
      let d := coreDirectionalDerivative hO hD (coordinateDirection j)
      |⟪(H*coefficientDerivative d B) U x,V x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ ∧
      |⟪(B*coefficientDerivative d H) U x,V x⟫_ℝ| ≤
        (C*eps)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖ := by
  obtain ⟨HN,hHN,hHnorm⟩ := exists_nativeH_uniform_half_norm_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨BN,hBN,hBnorm⟩ := exists_nativeBAngularAdjoint_uniform_half_norm_bound hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CH,hCH,hHform⟩ := exists_nativeH_uniform_half_angular_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  obtain ⟨CB,hCB,hBform⟩ := exists_nativeB_uniform_half_angular_smallness_forms hO hD hF g1 g2 hg1 hg2 L hL K hK
  let C := CB*HN+CH*BN
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall l i j U V H B d
  have hbpos : 0 < beta := by linarith
  have hnH := hHnorm lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l V
  have hnB := hBnorm lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall i V
  let BA := nativeBAngularAdjoint hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR
  let u := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖
  let v := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) V x‖
  have hu : 0 ≤ u := norm_nonneg _
  have hv : 0 ≤ v := norm_nonneg _
  have hc1 : CB*HN ≤ C := le_add_of_nonneg_right (mul_nonneg hCH.le hBN.le)
  have hc2 : CH*BN ≤ C := le_add_of_nonneg_left (mul_nonneg hCB.le hHN.le)
  constructor
  · change |⟪H (coefficientDerivative d B U) x,V x⟫_ℝ| ≤ _
    rw [nativeH_pointwise_inner_symm]
    have ht := (hBform lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall i j j U (H V)).2.1
    change |⟪coefficientDerivative d B U x,H V x⟫_ℝ| ≤ ((CB*eps/beta)*beta)*u*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (H V) x‖ at ht
    rw [div_mul_cancel₀ _ (ne_of_gt hbpos)] at ht
    calc
      _ ≤ (CB*eps)*u*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (H V) x‖ := ht
      _ ≤ (CB*eps)*u*(HN*v) := mul_le_mul_of_nonneg_left hnH (by positivity)
      _ = (CB*HN)*eps*u*v := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 heps) hu) hv
  · change |⟪B (coefficientDerivative d H U) x,V x⟫_ℝ| ≤ _
    rw [nativeB_pointwise_inner_adjoint]
    have ht := (hHform lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall l j j U (BA V)).2.1
    change |⟪coefficientDerivative d H U x,BA V x⟫_ℝ| ≤ (CH*beta)*u*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (BA V) x‖ at ht
    calc
      _ ≤ (CH*beta)*u*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (BA V) x‖ := ht
      _ ≤ (CH*beta)*u*((BN*eps/beta)*v) := mul_le_mul_of_nonneg_left hnB (by positivity)
      _ = (CH*BN)*eps*u*v := by field_simp [ne_of_gt hbpos] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 heps) hu) hv

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
