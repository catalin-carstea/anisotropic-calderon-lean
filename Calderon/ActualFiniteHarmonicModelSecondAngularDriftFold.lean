import Calderon.ActualFiniteHarmonicModelSecondBalancedAngularJets
import Calderon.ActualNormalizedSecondDriftDefectCoefficients
import Calderon.ActualFiniteHarmonicModelSecondAngularJets
import Calderon.ActualFiniteHarmonicModelSecondAngularBalancedBasis

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open ActualNormalizedSecondDriftDefectCoefficients ActualReferenceParallelRaising SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
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
lemma normalizedSecondDriftAngularConnectionNormalizedCoefficient_eq_native_expansion
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ) (x : R3) :
    normalizedSecondDriftAngularConnectionNormalizedCoefficient hO hD g1 g2 L lam δ R p x =
      referenceRadius δ R p L x • ∑ a : Fin 3,
        normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
          ((1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3,
            referenceFrameConnectionCoefficient g1 L lam x
              (referenceMetricGramFrame g1 L (lam,x) a) b c •
                ((normalizedRotation hO hD b c).comp (inverseDegreeMultiplier hO hD))) := by
  apply ContinuousLinearMap.ext
  intro u
  unfold normalizedSecondDriftAngularConnectionNormalizedCoefficient normalizedReferenceAngularConnection
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    Finset.smul_sum,smul_smul,mul_assoc]


lemma nativeWSecondBalancedAngularCoefficient_eq_full_zeroDrift
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ):
    nativeWSecondBalancedAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p =
      fun x =>
    let h := referenceNormalizedPrincipalDifference g1 g2 L lam
    let I := inverseDegreeMultiplier hO hD
    let Id := ContinuousLinearMap.id ℝ SphereL2
    let mu := fun y : R3 => referenceDensityFamily g1 L (lam,y)
    let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
    (adjointZeroCoefficient coordinateDirection mu (actualPrincipalMatrix g1 L lam δ R p h) x) •
      (I.comp I) -
    (mu x)⁻¹ • ∑ j : Fin 3,
      (weightedAngularAdjointDerivative (coordinateDirection j) mu
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j) x).comp I +
    (ContinuousLinearMap.adjoint (K0 x) - K0 x) +
    (∑ a : Fin 3, physicalMixedDensityCorrection g1 L lam h a x •
      ((balancedDerivative hF hO hD a).comp I)) +
    ((∑ a : Fin 3, physicalMixedProfileCoefficient g1 L lam δ R p h a x •
      ((balancedDerivative hF hO hD a).comp (Id - (2 : ℝ) • I))) -
      (∑ a : Fin 3, physicalMixedProfileCoefficient g1 L lam δ R p h a x •
        ((balancedRaising hF hO hD a).comp (Id - I)))) +
    ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (-physicalMixedConnectionCoefficient g1 L lam h a b c x) •
        ((normalizedRotation hO hD b c).comp
          ((balancedDerivative hF hO hD a).comp (Id - I)))) -
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        physicalMixedConnectionCoefficient g1 L lam h a b c x •
          ((balancedRaising hF hO hD a).comp (normalizedRotation hO hD b c)))) +
    ((∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g1 L lam δ R p h a b x •
      ((balancedDerivative hF hO hD b).comp
        ((balancedDerivative hF hO hD a).comp (Id - I)))) -
      (∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g1 L lam δ R p h a b x •
        ((balancedRaising hF hO hD a).comp
          ((balancedRaising hF hO hD b).comp (Id + I))))) +
    normalizedSecondDriftDefectZeroNormalizedCoefficient hO hD g1 g2 L lam δ R p x := by
  funext x
  dsimp only [nativeWSecondBalancedAngularCoefficient]
  unfold normalizedSecondDriftDefectZeroNormalizedCoefficient
  rw [← normalizedSecondDriftAngularConnectionNormalizedCoefficient_eq_native_expansion hO hD g1 g2 L lam δ R p x]
  exact add_sub_assoc _ _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
