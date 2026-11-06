import Calderon.ActualFiniteHarmonicModelPointwiseAngularAdjoints
import Calderon.ActualFiniteHarmonicModelBDerivativeAngularForm
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
  ReferenceDensityBounds NormalizedPrincipalMetric ActualScalarPrincipalAdjoint
  ActualNormalizedSecondMetricDrift PrincipalCommutator ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev bAngularAdjointFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] bAngularAdjointFunction


def nativeBAngularAdjoint
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD (fun x => adjointFirstCoefficient coordinateDirection
    (fun y => referenceDensityFamily g1 L (lam,y))
    (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j)
    (contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j)-
    nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR-
    nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR

lemma nativeBAngularAdjoint_preserving_derivative_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeBAngularAdjoint hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x).adjoint
        (coreWeightOperator hO hD (besselWeight 1) F x)+
      (∑ a : Fin 3, physicalMixedFirstCoefficient g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x • coreDerivative hO hD hF a F x)+
      normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  have hJ : normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 L lam δ R p j x
      (coreWeightOperator hO hD (besselWeight 1) F x) =
      (referenceRadius δ R p L x*normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) • F x := by
    simp only [normalizedSecondDriftFirstNormalizedCoefficient,ContinuousLinearMap.smul_apply,
      inverseDegreeMultiplier_coreWeight_one_apply hO hD F x]
  change _ - nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x-
    nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x = _
  rw [nativeB_preserving_raising_action,nativeV_firstAngular_action,hJ]
  change _ • F x-(_+(∑ a : Fin 3, _ • coreRaising hO hD hF a F x)+_)-_ = _
  simp only [ContinuousLinearMap.add_apply,Fin.sum_univ_three,smul_add]
  module

lemma nativeB_pointwise_inner_adjoint
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x,G x⟫_ℝ =
      ⟪F x,nativeBAngularAdjoint hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR G x⟫_ℝ := by
  let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) j x
  have hK : PreservesSphereSpectralGraphs hO hD K :=
    preservesSphereSpectralGraphs_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p _ j x
  have hk := inner_preserving_weight_one_adjoint hO hD K hK F G x
  have hr (a : Fin 3) : ⟪coreRaising hO hD hF a F x,G x⟫_ℝ =
      ⟪F x,coreDerivative hO hD hF a G x⟫_ℝ := by
    have ht := AngularShiftGraph.sphereDerivativeGraph_inner_adjoint hF hO hD a
      (G x) (coreDerivative hO hD hF a G x) (F x) (coreRaising hO hD hF a F x)
      (coreDerivative_graph hO hD hF a G x) (coreRaising_graph hO hD hF a F x)
    rw [real_inner_comm,← ht]
    exact real_inner_comm _ _
  rw [nativeB_preserving_raising_action,nativeBAngularAdjoint_preserving_derivative_action]
  simp only [inner_add_left,inner_add_right,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  rw [hk]
  simp only [hr]
  congr 1
  simp only [normalizedSecondDriftFirstNormalizedCoefficient,ContinuousLinearMap.smul_apply,
    inverseDegreeMultiplier_coreWeight_one_apply hO hD F x,
    inverseDegreeMultiplier_coreWeight_one_apply hO hD G x,
    real_inner_smul_left,real_inner_smul_right]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
