import Calderon.ActualFiniteHarmonicModelDriftZeroMassBounds
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
private abbrev driftConnectionRawFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] driftConnectionRawFunction

def nativeDriftConnectionRawAction
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD (referenceRadius δ R p L) (contDiff_referenceRadius_actual δ R p L hδ hR)*
    ∑ a : Fin 3, coreScalar hO hD (fun y => normalizedSecondDriftFrameJoint g1 g2 L a (lam,y))
      ((contDiff_normalizedSecondDriftFrameJoint g1 g2 hg1 hg2 L a).comp (contDiff_const.prodMk contDiff_id))*
      nativeReferenceConnectionAction hO hD g1 hg1 L lam a

lemma hasCoreScalarExpansionBound_nativeDriftConnectionRawAction
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (nativeDriftConnectionRawAction hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR) x
      (nativeDriftZeroRawMass g1 g2 L lam δ R p x) := by
  unfold nativeDriftConnectionRawAction nativeDriftZeroRawMass
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ _
    (hasCoreScalarExpansionBound_nativeReferenceConnectionAction hO hD hF g1 hg1 L lam a x)
  unfold nativeReferenceWeightedZeroRawMass
  exact le_add_of_nonneg_right (abs_nonneg _)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
