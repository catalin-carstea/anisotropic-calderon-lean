import Calderon.ActualFiniteHarmonicModelReferenceCovectorZeroExpansion
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondMetricDrift
  ActualReferenceDDSpectralTransport ConformalDepth ActualScalarPrincipalAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev driftZeroRawFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] driftZeroRawFunction

def nativeDriftZeroRawAction
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD (referenceRadius δ R p L) (contDiff_referenceRadius_actual δ R p L hδ hR)*
    ∑ a : Fin 3, coreScalar hO hD (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y))
      ((contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp (contDiff_const.prodMk contDiff_id))*
      (nativeReferenceConnectionAction hO hD g1 hg1 L lam a+
        nativeReferenceProfileScalar hO hD g1 hg1 L lam δ R p hδ hR a*coreDegree hO hD)

def nativeDriftZeroRawMass (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) : ℝ :=
  |referenceRadius δ R p L x| * (∑ a : Fin 3, |normalizedSecondDriftFrameJoint g1 g2 L a (lam,x)| *
    nativeReferenceWeightedZeroRawMass g1 L lam δ R p a x)

lemma nativeDriftZeroRawAction_apply
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeDriftZeroRawAction hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR F x =
      normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  have h12 : (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1 := by
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1) (coreWeightOperator hO hD (besselWeight 1) F) x
  have hi := BoundedAngularShift.inverseDegreeMultiplier_of_besselGraph hO hD _ _ h12
  unfold nativeDriftZeroRawAction normalizedSecondDriftZeroNormalizedCoefficient
  simp only [Module.End.mul_apply,LinearMap.sum_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,Submodule.coe_sum,Finset.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,hi]
  simp_rw [referenceWeightedZeroBaseNormalizedCoefficient_coreWeight_one_apply hO hD g1 hg1 L lam δ R p hδ hR]

lemma hasCoreScalarExpansionBound_nativeDriftZeroRawAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeDriftZeroRawAction hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR) x
      (nativeDriftZeroRawMass g1 g2 L lam δ R p x) := by
  unfold nativeDriftZeroRawAction nativeDriftZeroRawMass
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  exact hasCoreScalarExpansionBound_scalar_mul hO hD _ _ x _
    (hasCoreScalarExpansionBound_nativeReferenceWeightedZeroRaw hO hD hF g1 hg1 L lam δ R p hδ hR a x) _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
