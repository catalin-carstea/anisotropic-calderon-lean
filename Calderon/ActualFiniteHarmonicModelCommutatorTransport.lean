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
lemma nativeFirstDefect_commutator_eq_model (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ActualModelCommutatorWords.commutator
      (2 * (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR - nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) +
        (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR - nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
      (nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) =
    ActualModelCommutatorWords.commutator (modelFirstOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR))
      (modelSecondOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) := by
  exact congrArg₂ (ActualModelCommutatorWords.commutator
    (A := Module.End ℝ (smoothCompactFiniteSphereCore hO hD)))
    (nativeFirstDefect_eq_modelFirstOrder hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (nativeU_eq_modelSecondOrder hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
