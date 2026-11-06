import Calderon.ActualFiniteHarmonicModelCBalancedForms
import Calderon.ActualFiniteHarmonicModelZeroAngularJets

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  BalancedAngularShift ActualReferenceDDHigherGeometryJets SectionFiveErrorForms
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
private abbrev nativeWBalancedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWBalancedFunction
lemma nativeC_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x,G x⟫_ℝ =
      ⟪nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [nativeC_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x]
  exact coordinateFieldWordPartial_nativeC_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR [] F G x


lemma coefficientDerivative_nativeC_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (i : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪ActualModelCommutatorWords.coefficientDerivative
        (coreDirectionalDerivative hO hD (coordinateDirection i))
        (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x,G x⟫_ℝ =
      ⟪directionalFDeriv (coordinateDirection i)
        (nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [coefficientDerivative_nativeC_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
    (coordinateDirection i) F x]
  exact coordinateFieldWordPartial_nativeC_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR [i] F G x


lemma coefficientDerivative_second_nativeC_secondAngular_inner_threehalf_half
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (i k : Fin 3) (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ⟪ActualModelCommutatorWords.coefficientDerivative
        (coreDirectionalDerivative hO hD (coordinateDirection i))
        (ActualModelCommutatorWords.coefficientDerivative
          (coreDirectionalDerivative hO hD (coordinateDirection k))
          (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) F x,G x⟫_ℝ =
      ⟪directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection k)
          (nativeCSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p)) x
        (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x),
        coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x⟫_ℝ := by
  rw [coefficientDerivative_second_nativeC_secondAngular_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
    (coordinateDirection i) (coordinateDirection k) F x]
  exact coordinateFieldWordPartial_nativeC_secondAngular_inner_threehalf_half hO hD hF g1 g2 hg1
    L lam δ R p hg2 hδ hR [i,k] F G x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
