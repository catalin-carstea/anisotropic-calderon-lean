import Calderon.ActualFiniteHarmonicModelAngularCompositionForms
import Calderon.ActualFiniteHarmonicModelFirstCoefficientJets

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
  ReferenceDensityBounds NormalizedPrincipalMetric
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev bDerivativeAngularFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] bDerivativeAngularFunction

lemma nativeB_preserving_raising_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
        (coreWeightOperator hO hD (besselWeight 1) F x) +
      (∑ b : Fin 3, physicalMixedFirstCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) b j x • coreRaising hO hD hF b F x) +
      normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  rw [nativeB_firstNormalizedCoefficient_apply]
  simp only [modelFirstNormalizedCoefficient,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,coreRaising,
    Module.End.mul_apply,coreNormalizedRaising,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]

lemma abs_inner_nativeB_coreDerivative_le_half_threehalf
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j a : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
    let J := normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
    let m (b : Fin 3) := physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) b j x
    |⟪nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
      (coreDerivative hO hD hF a F) x,G x⟫_ℝ| ≤
      (4*(‖K‖+‖J‖)+8*∑ b : Fin 3, |m b|) *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖ := by
  intro K J m
  let H := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖
  let V := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖
  let W := coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF a F) x
  have hK : PreservesSphereSpectralGraphs hO hD K :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD
      g1 hg1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
  have hJ : PreservesSphereSpectralGraphs hO hD J := by
    unfold J normalizedSecondDriftFirstNormalizedCoefficient
    exact preservesSphereSpectralGraphs_smul hO hD _ _
      (preservesSphereSpectralGraphs_inverseDegreeMultiplier hO hD)
  have hKb : |⟪K W,G x⟫_ℝ| ≤ (4*‖K‖)*H*V :=
    abs_inner_preserving_weight_derivative_le_half_threehalf hO hD hF a K hK F G x
  have hJb : |⟪J W,G x⟫_ℝ| ≤ (4*‖J‖)*H*V :=
    abs_inner_preserving_weight_derivative_le_half_threehalf hO hD hF a J hJ F G x
  have hmb (b : Fin 3) :
      |m b*⟪coreRaising hO hD hF b (coreDerivative hO hD hF a F) x,G x⟫_ℝ| ≤
        (8*|m b|)*H*V := by
    rw [abs_mul]
    have ht := mul_le_mul_of_nonneg_left
      (abs_inner_raising_derivative_le_half_threehalf hO hD hF a b F G x) (abs_nonneg (m b))
    calc
      _ ≤ |m b| *(8*H*V) := ht
      _ = _ := by ring
  rw [nativeB_preserving_raising_action,inner_add_left,inner_add_left,sum_inner]
  simp only [real_inner_smul_left]
  change |⟪K W,G x⟫_ℝ + (∑ b : Fin 3, m b*⟪coreRaising hO hD hF b
    (coreDerivative hO hD hF a F) x,G x⟫_ℝ) + ⟪J W,G x⟫_ℝ| ≤ _
  calc
    _ ≤ |⟪K W,G x⟫_ℝ| + |∑ b : Fin 3, m b*⟪coreRaising hO hD hF b
      (coreDerivative hO hD hF a F) x,G x⟫_ℝ| + |⟪J W,G x⟫_ℝ| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (4*‖K‖)*H*V + (∑ b : Fin 3, (8*|m b|)*H*V) + (4*‖J‖)*H*V := by
      apply add_le_add (add_le_add hKb ?_) hJb
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => hmb b))
    _ = _ := by simp only [← Finset.sum_mul,← Finset.mul_sum]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
