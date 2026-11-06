import Calderon.ActualFiniteHarmonicModelFirstDefect
import Calderon.ActualFiniteHarmonicCoreFirstSecondWords

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients
  ActualScalarPrincipalAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothSphereFields SmoothAngularApplication
  ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
lemma native_model_first_second_order_commutator_words (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ActualModelCommutatorWords.commutator (modelFirstOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
      (modelSecondOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) =
  secondBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) +
    firstBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) +
    zeroBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  have hw := core_first_second_order_commutator_words hO hD
    (fun i => coreDirectionalDerivative hO hD (coordinateDirection i))
    (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)
    (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (fun i j => coreDirectionalDerivative_commute hO hD (coordinateDirection i) (coordinateDirection j))
    (nativeH_commute_principal hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeH0_commute_principal hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
  exact hw

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
