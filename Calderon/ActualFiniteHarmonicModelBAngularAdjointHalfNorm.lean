import Calderon.ActualFiniteHarmonicModelBAngularAdjoint
import Calderon.ActualFiniteHarmonicModelHalfWeightSumAction
import Calderon.ActualFiniteHarmonicModelBDerivativeFormCoefficientBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelErrorAssembly
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualReferenceDDSpectralTransport ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients ActualPhysicalMixedFirst
  ReferenceDensityBounds NormalizedPrincipalMetric ActualScalarPrincipalAdjoint
  ActualNormalizedSecondMetricDrift PrincipalCommutator ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev bAdjointHalfNormFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] bAdjointHalfNormFunction


lemma norm_coreWeight_half_nativeBAngularAdjoint_le
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
    let J := normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
    let m (a : Fin 3) := physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x
    ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
      (nativeBAngularAdjoint hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F) x‖ ≤
      (‖K‖+‖J‖+2*∑ a : Fin 3, |m a|)*
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  intro K J m
  let M := K.adjoint+J
  have hK : PreservesSphereSpectralGraphs hO hD K :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p _ j x
  have hJ : PreservesSphereSpectralGraphs hO hD J := by
    unfold J normalizedSecondDriftFirstNormalizedCoefficient
    exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  have hM : PreservesSphereSpectralGraphs hO hD M :=
    preservesSphereSpectralGraphs_add hO hD _ _
      (preservesSphereSpectralGraphs_adjoint hO hD K hK) hJ
  have hA : nativeBAngularAdjoint hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      M (coreWeightOperator hO hD (besselWeight 1) F x)+
        ∑ a : Fin 3, m a • coreDerivative hO hD hF a F x := by
    rw [nativeBAngularAdjoint_preserving_derivative_action]
    dsimp only [M,K,J,m]
    rw [ContinuousLinearMap.add_apply]
    abel
  have ht := norm_coreWeight_half_le_preserving_add_sum hO hD M hM _ F
    (fun a => coreDerivative hO hD hF a F) m (fun _ => 2) x hA
    (fun a => norm_coreWeight_half_derivative_le hO hD hF a F x)
  have hn : ‖M‖ ≤ ‖K‖+‖J‖ := by
    have he : ‖K.adjoint‖ = ‖K‖ :=
      (ContinuousLinearMap.adjoint : (SphereL2 →L[ℝ] SphereL2) ≃ₗᵢ[ℝ]
        (SphereL2 →L[ℝ] SphereL2)).norm_map K
    simpa only [he] using norm_add_le K.adjoint J
  have hs : (∑ a : Fin 3, |m a| * 2) = 2*∑ a : Fin 3, |m a| := by
    rw [← Finset.sum_mul,mul_comm]
  rw [hs] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right (add_le_add hn le_rfl) (norm_nonneg _))

theorem exists_nativeBAngularAdjoint_uniform_half_norm_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := ReferenceWeightedApproximation.actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      CoordinateBootstrapJets.coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ j : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD,
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
        (nativeBAngularAdjoint hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F) x‖ ≤
        (C*eps/beta)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_nativeB_derivative_form_coefficient_uniform_smallness
    hO hD g1 g2 hg1 hg2 L hL K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall j F
  have hc := hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx hb hH8 hsmall j
  let KK := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
  let J := normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
  let S := ∑ a : Fin 3, |physicalMixedFirstCoefficient g1 L lam
    (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hKn : 0 ≤ ‖KK‖ := norm_nonneg _
  have hJn : 0 ≤ ‖J‖ := norm_nonneg _
  change 4*(‖KK‖+‖J‖)+8*S ≤ C*eps/beta at hc
  have hc' : ‖KK‖+‖J‖+2*S ≤ C*eps/beta := by linarith
  exact (norm_coreWeight_half_nativeBAngularAdjoint_le hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x).trans
    (mul_le_mul_of_nonneg_right hc' (norm_nonneg _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
