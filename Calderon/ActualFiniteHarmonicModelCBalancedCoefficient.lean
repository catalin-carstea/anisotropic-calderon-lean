import Calderon.ActualFiniteHarmonicModelZeroAngularNormalization
import Calderon.ActualFiniteHarmonicModelSecondAngularBalancedBasis
import Calderon.ActualFiniteHarmonicModelSecondAngularNormalization
import Calderon.ActualNormalizedSecondDriftWeightedCoefficients

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualNormalizedSphereRotation ActualReferenceDDNormalizedCoefficient
  ActualReferenceDDSpectralTransport ActualReferenceDDHigherSpectralGraphs
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondModelDefectCoefficients
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ActualScalarPrincipalAdjoint NaturalAngularAdjoint ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftNativeAdjunction ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftWeightedCoefficients ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothMetricFrame MovingFrameConnection SmoothSphereFields
  SmoothAngularApplication
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeCSecondFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeCSecondFunction
def nativeCSecondBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x =>
    let h := referenceNormalizedPrincipalDifference g1 g2 L lam
    let I := inverseDegreeMultiplier hO hD
    let Id := ContinuousLinearMap.id ℝ SphereL2
    referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h x +
    (∑ a : Fin 3, physicalMixedProfileCoefficient g1 L lam δ R p h a x •
      ((balancedRaising hF hO hD a).comp (Id - I))) +
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      physicalMixedConnectionCoefficient g1 L lam h a b c x •
        ((balancedRaising hF hO hD a).comp (normalizedRotation hO hD b c))) +
    (∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g1 L lam δ R p h a b x •
      ((balancedRaising hF hO hD a).comp
        ((balancedRaising hF hO hD b).comp (Id + I)))) +
    normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p x

lemma contDiff_nativeCSecondBalancedAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hhentry (i j : Fin 3) : ContDiff ℝ ∞ (fun y => h y i j) :=
    (contDiff_apply_apply ℝ ℝ i j).comp hh
  let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
  have hK0 : ContDiff ℝ ∞ K0 :=
    contDiff_referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p
      hδ hR h hh
  have hprof (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedProfileCoefficient g1 L lam δ R p h a) :=
    contDiff_physicalMixedProfileCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a
  have hconn (a b c : Fin 3) : ContDiff ℝ ∞ (physicalMixedConnectionCoefficient g1 L lam h a b c) :=
    contDiff_physicalMixedConnectionCoefficient g1 hg1 L lam h hhentry a b c
  have hpure (a b : Fin 3) : ContDiff ℝ ∞ (physicalPureAngularCoefficient g1 L lam δ R p h a b) :=
    contDiff_physicalPureAngularCoefficient g1 hg1 L lam δ R p h hδ hR hhentry a b
  have hJ0 : ContDiff ℝ ∞
      (normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 L lam δ R p) :=
    contDiff_normalizedSecondDriftZeroNormalizedCoefficient hO hD g1 g2 hg1 hg2
      L lam δ R p hδ hR
  unfold nativeCSecondBalancedAngularCoefficient
  dsimp only
  exact ((((hK0.add
    (ContDiff.sum fun a _ => (hprof a).smul contDiff_const)).add
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ => ContDiff.sum fun c _ =>
      (hconn a b c).smul contDiff_const)).add
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ => (hpure a b).smul contDiff_const)).add hJ0)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
