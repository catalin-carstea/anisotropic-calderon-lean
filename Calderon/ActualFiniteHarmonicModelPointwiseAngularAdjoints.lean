import Calderon.ActualFiniteHarmonicModelFirstAngularNormalization
import Calderon.ActualFiniteHarmonicModelAngularCompositionForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  AngularShiftGraph ActualReferenceDDSpectralTransport ActualReferenceDDNormalizedCoefficient
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev pointwiseAdjointFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] pointwiseAdjointFunction

lemma inner_preserving_weight_one_adjoint
    (M : SphereL2 →L[ℝ] SphereL2) (hM : PreservesSphereSpectralGraphs hO hD M)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪M (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪F x,M.adjoint (coreWeightOperator hO hD (besselWeight 1) G x)⟫_ℝ := by
  rw [← M.adjoint_inner_right]
  exact spectralGraph_inner_symm hO hD (besselWeight 1)
    (F x) (coreWeightOperator hO hD (besselWeight 1) F x)
    (M.adjoint (G x)) (M.adjoint (coreWeightOperator hO hD (besselWeight 1) G x))
    (coreWeightOperator_graph hO hD (besselWeight 1) F x)
    (preservesSphereSpectralGraphs_adjoint hO hD M hM _ _ _
      (coreWeightOperator_graph hO hD (besselWeight 1) G x))

lemma inner_coreDerivative_add_coreRaising_symm
    (hF : SphereFischerInner) (a : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪coreDerivative hO hD hF a F x+coreRaising hO hD hF a F x,G x⟫_ℝ =
      ⟪F x,coreDerivative hO hD hF a G x+coreRaising hO hD hF a G x⟫_ℝ := by
  have h1 := sphereDerivativeGraph_inner_adjoint hF hO hD a
    (F x) (coreDerivative hO hD hF a F x) (G x) (coreRaising hO hD hF a G x)
    (coreDerivative_graph hO hD hF a F x) (coreRaising_graph hO hD hF a G x)
  have h2 := sphereDerivativeGraph_inner_adjoint hF hO hD a
    (G x) (coreDerivative hO hD hF a G x) (F x) (coreRaising hO hD hF a F x)
    (coreDerivative_graph hO hD hF a G x) (coreRaising_graph hO hD hF a F x)
  rw [inner_add_left,inner_add_right,h1]
  have h2' : ⟪coreRaising hO hD hF a F x,G x⟫_ℝ =
      ⟪F x,coreDerivative hO hD hF a G x⟫_ℝ := by
    rw [real_inner_comm,← h2]
    exact real_inner_comm _ _
  rw [h2']
  exact add_comm _ _

lemma nativeH_pointwise_inner_symm
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x,G x⟫_ℝ =
      ⟪F x,nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j G x⟫_ℝ := by
  let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    (NormalizedPrincipalMetric.referenceNormalizedPrincipalDifference g1 g2 L lam) j x
  have hK : PreservesSphereSpectralGraphs hO hD K :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient
      hO hD g1 hg1 L lam δ R p _ j x
  have h1 := inner_preserving_weight_one_adjoint hO hD K hK F G x
  have h2 := inner_preserving_weight_one_adjoint hO hD K.adjoint
    (preservesSphereSpectralGraphs_adjoint hO hD K hK) F G x
  have hw : ⟪(K+K.adjoint) (coreWeightOperator hO hD (besselWeight 1) F x),G x⟫_ℝ =
      ⟪F x,(K+K.adjoint) (coreWeightOperator hO hD (besselWeight 1) G x)⟫_ℝ := by
    rw [ContinuousLinearMap.add_apply,inner_add_left,h1,h2,
      ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.add_apply,inner_add_right]
    exact add_comm _ _
  rw [nativeH_apply_eq_firstAngularField,nativeH_apply_eq_firstAngularField]
  unfold nativeHFirstAngularField
  rw [inner_add_left,inner_sub_left,inner_add_right,inner_sub_right,hw]
  congr 1
  · congr 1
    rw [sum_inner,inner_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [real_inner_smul_left,real_inner_smul_right,
      inner_coreDerivative_add_coreRaising_symm hO hD hF]
  · rw [real_inner_smul_left,real_inner_smul_right]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
