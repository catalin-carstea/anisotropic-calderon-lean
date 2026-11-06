import Calderon.ActualFiniteHarmonicModelSecondAngularJets
import Calderon.ActualFiniteHarmonicModelSecondAngularAdjointBasis
import Calderon.ActualFiniteHarmonicModelFirstAngularBounds
import Calderon.ActualNormalizedSecondDriftDefectCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift BalancedAngularShift
  ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherCLMProducts
  ActualReferenceDDHigherSpectralGraphs ActualReferenceDDSpectralTransport ActualReferenceDDNormalizedCoefficient
  ActualReferenceParallelRaising ActualNormalizedSphereRotation ActualScalarPrincipalAdjoint NaturalAngularAdjoint
  ActualNormalizedSecondModelErrorAssembly ActualNormalizedSecondDriftNativeAdjunction
  ActualNormalizedSecondDriftDefectCoefficients ActualNormalizedSecondDriftDefectWeightedJets ActualNormalizedSecondMetricDrift
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection ActualPhysicalPureAngular
  ReferenceDensityBounds NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  SmoothMetricFrame MovingFrameConnection PrincipalCommutator ConformalDepth SectionFiveErrorForms
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeWSymmetricFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWSymmetricFunction
def nativeWSymmetricHalfAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun y =>
    let h := referenceNormalizedPrincipalDifference g1 g2 L lam
    let mu := fun z : R3 => referenceDensityFamily g1 L (lam,z)
    let Y := fun j : Fin 3 => weightedAngularAdjointDerivative (coordinateDirection j) mu
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j)
    (adjointZeroCoefficient coordinateDirection mu (actualPrincipalMatrix g1 L lam δ R p h) y -
      normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p y) •
        ((2 : ℝ) • inverseDegreeMultiplier hO hD) -
    (mu y)⁻¹ • ∑ j : Fin 3, (Y j y + ContinuousLinearMap.adjoint (Y j y)) +
    ∑ a : Fin 3, physicalMixedDensityCorrection g1 L lam h a y •
      (balancedDerivative hF hO hD a + balancedRaising hF hO hD a)

lemma contDiff_nativeWSymmetricHalfAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeWSymmetricHalfAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h := contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  let mu : R3 → ℝ := fun z => referenceDensityFamily g1 L (lam,z)
  have hmu : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  have hmui : ContDiff ℝ ∞ (fun z => (mu z)⁻¹) :=
    (contDiff_referenceDensityFamily_inv g1 hg1 L).comp (contDiff_const.prodMk contDiff_id)
  let B (j : Fin 3) := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j
  have hB (j : Fin 3) : ContDiff ℝ ∞ (B j) :=
    contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p hδ hR h hh j
  let Y (j : Fin 3) := weightedAngularAdjointDerivative (coordinateDirection j) mu (B j)
  have hY (j : Fin 3) : ContDiff ℝ ∞ (Y j) :=
    contDiff_directionalFDeriv (coordinateDirection j) _ (hmu.smul (contDiff_angularAdjoint (B j) (hB j)))
  have hYa (j : Fin 3) : ContDiff ℝ ∞ (fun z => ContinuousLinearMap.adjoint (Y j z)) :=
    contDiff_angularAdjoint (Y j) (hY j)
  have hA := contDiff_modelAdjointZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hDiv := contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR
  have hDens (a : Fin 3) := contDiff_physicalMixedDensityCorrection g1 hg1 L lam h
    (fun i j => (contDiff_apply_apply ℝ ℝ i j).comp hh) a
  unfold nativeWSymmetricHalfAngularCoefficient
  exact (((hA.sub hDiv).smul contDiff_const).sub
    (hmui.smul (ContDiff.sum fun j _ => (hY j).add (hYa j)))).add
      (ContDiff.sum fun a _ => (hDens a).smul contDiff_const)


end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
