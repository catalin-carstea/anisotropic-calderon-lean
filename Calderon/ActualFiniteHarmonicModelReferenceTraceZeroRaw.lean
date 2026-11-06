import Calderon.ActualFiniteHarmonicModelReferenceCovectorZeroExpansion
import Calderon.ActualFiniteHarmonicModelReferenceWeightedFirstScalars

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualReferenceDDNormalizedCoefficient ActualPhysicalMixedReferenceCancellation
  ConformalDepth ActualScalarPrincipalAdjoint
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceTraceRawFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] referenceTraceRawFunction

def nativeReferenceTraceZeroRawAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD (referenceRadius δ R p L) (contDiff_referenceRadius_actual δ R p L hδ hR)*
    ∑ a : Fin 3, ∑ b : Fin 3, coreScalar hO hD (physicalMixedQFrameCoefficient g L lam h a b)
      (contDiff_physicalMixedQFrameCoefficient g hg L lam h
        (fun i j => (contDiff_apply_apply ℝ ℝ i j).comp hh) a b)*
      nativeReferenceCovectorZeroRawAction hO hD g hg L lam δ R p hδ hR a b

def nativeReferenceTraceZeroRawMass (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (x : R3) : ℝ :=
  |referenceRadius δ R p L x| * (∑ a : Fin 3, ∑ b : Fin 3,
    |physicalMixedQFrameCoefficient g L lam h a b x| *nativeReferenceCovectorZeroRawMass g L lam δ R p a b x)

lemma nativeReferenceTraceZeroRawAction_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeReferenceTraceZeroRawAction hO hD g hg L lam δ R p h hh hδ hR F x =
      referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g hg L lam δ R p h x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  unfold nativeReferenceTraceZeroRawAction referenceWeightedZeroBaseNormalizedCoefficientTrace
  simp only [Module.End.mul_apply,LinearMap.sum_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,Submodule.coe_sum,Finset.sum_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply]
  simp_rw [referenceCovectorZeroBaseNormalizedCoefficient_coreWeight_two_apply hO hD g hg L lam δ R p hδ hR]

lemma hasCoreScalarExpansionBound_nativeReferenceTraceZeroRawAction
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hh : ContDiff ℝ ∞ h) (hδ : 0 < δ) (hR : 0 < R) (x : R3) :
    HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2)
      (nativeReferenceTraceZeroRawAction hO hD g hg L lam δ R p h hh hδ hR) x
      (nativeReferenceTraceZeroRawMass g L lam δ R p h x) := by
  unfold nativeReferenceTraceZeroRawAction nativeReferenceTraceZeroRawMass
  apply hasCoreScalarExpansionBound_scalar_mul hO hD
  apply hasCoreScalarExpansionBound_sum hO hD
  intro a _
  apply hasCoreScalarExpansionBound_sum hO hD
  intro b _
  exact hasCoreScalarExpansionBound_scalar_mul hO hD _ _ x _
    (hasCoreScalarExpansionBound_nativeReferenceCovectorZeroRawAction hO hD hF g hg L lam δ R p hδ hR a b x)
    _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
