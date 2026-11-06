import Calderon.ActualFiniteHarmonicModelPointwiseAngularAdjoints

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SpectralCoreRegularity
  AngularShiftGraph ActualReferenceDDSpectralTransport ActualReferenceDDNormalizedCoefficient
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev vPointwiseAdjointFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] vPointwiseAdjointFunction

lemma nativeV_pointwise_inner_symm
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x,G x⟫_ℝ =
      ⟪F x,nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR G x⟫_ℝ := by
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
  dsimp only [K] at hw
  rw [nativeV_firstAngular_action,nativeV_firstAngular_action]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hw]
  congr 2
  rw [sum_inner,inner_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [real_inner_smul_left,real_inner_smul_right,
    inner_coreDerivative_add_coreRaising_symm hO hD hF]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
