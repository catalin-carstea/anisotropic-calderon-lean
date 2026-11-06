import Calderon.ActualFiniteHarmonicModelQuadraticAdjointTransfer
import Calderon.ActualFiniteHarmonicModelReferenceTraceZeroMassBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDSpectralTransport
  ActualReferenceDDHigherSpectralGraphs NaturalAngularAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev traceAdjointExpansionFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] traceAdjointExpansionFunction

def nativeReferenceTraceZeroAdjointRawAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreCoefficientAction hO hD
    (fun x => (referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x).adjoint)
    (contDiff_angularAdjoint _
      (contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p hδ hR h hh))
    (fun x => preservesSphereSpectralGraphs_adjoint hO hD _
      (preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x)) *
    coreWeightOperator hO hD (besselWeight 2)

lemma nativeReferenceTraceZeroRawAction_inner_adjoint
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeReferenceTraceZeroRawAction hO hD g hg L lam δ R p h hh hδ hR F x,G x⟫_ℝ =
      ⟪F x,nativeReferenceTraceZeroAdjointRawAction hO hD g hg L lam δ R p h hh hδ hR G x⟫_ℝ := by
  rw [nativeReferenceTraceZeroRawAction_apply]
  exact inner_preserving_weight_adjoint hO hD _
    (preservesSphereSpectralGraphs_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x) 2 F G x

lemma hasCoreScalarExpansionBound_nativeReferenceTraceZeroAdjointRawAction
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (nativeReferenceTraceZeroAdjointRawAction hO hD g hg L lam δ R p h hh hδ hR) x
      (nativeReferenceTraceZeroRawMass g L lam δ R p h x) := by
  exact hasCoreScalarExpansionBound_pointwise_adjoint hO hD hF _ _
    (nativeReferenceTraceZeroRawAction_inner_adjoint hO hD g hg L lam δ R p h hh hδ hR) x _
    (hasCoreScalarExpansionBound_nativeReferenceTraceZeroRawAction hO hD hF g hg L lam δ R p h hh hδ hR x)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
