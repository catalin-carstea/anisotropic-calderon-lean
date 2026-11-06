import Calderon.ActualFiniteHarmonicModelZeroAngularNormalization
import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
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
private abbrev nativeCSecondJetFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeCSecondJetFunction
lemma coefficientDerivative_nativeC_secondAngular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x =
      directionalFDeriv v (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 2) F
  have hact : (fun y => nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F y) =
      (fun y => (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) y (U y)) :=
    funext (fun y => nativeC_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F y)
  have hW : coreWeightOperator hO hD (besselWeight 2) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change directionalFDeriv v (fun y => nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F y) x -
      nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,nativeC_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) (U : R3 → SphereL2)
    (contDiff_nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) U.property.1 x,hW]
  abel


lemma coefficientDerivative_second_nativeC_secondAngular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD v)
      (ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u)
        (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x =
      directionalFDeriv v (directionalFDeriv u
        (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p)) x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 2) F
  let A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    ActualModelCommutatorWords.coefficientDerivative (coreDirectionalDerivative hO hD u) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      A G y = directionalFDeriv u (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) y
        (coreWeightOperator hO hD (besselWeight 2) G y) :=
    coefficientDerivative_nativeC_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR u G y
  have hact : (fun y => A F y) =
      (fun y => directionalFDeriv u (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) y (U y)) :=
    funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 2) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change directionalFDeriv v (fun y => A F y) x - A (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p))
    (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u _ (contDiff_nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
    U.property.1 x,hW]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
