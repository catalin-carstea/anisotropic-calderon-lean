import Calderon.ActualFiniteHarmonicModelFirstCoefficientJets
import Calderon.ActualFiniteHarmonicModelReferenceDefectSecondAngularDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualModelCommutatorWords ActualNormalizedSecondModelCoefficients PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeBZDerivativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeBZDerivativeFunction

def nativeBZFirstDerivativeSecondAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (v : R3) :
    R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x).comp
    (directionalFDeriv v
      (nativeReferenceDefectSecondAngularCoefficient hO hD hF g1 L lam δ R p) x)

lemma nativeB_coefficientDerivative_nativeZ_secondAngularCoefficient_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ)
    (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (v : R3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      coefficientDerivative (coreDirectionalDerivative hO hD v)
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) F x =
      nativeBZFirstDerivativeSecondAngularCoefficient hO hD hF g1 g2 hg1
        L lam δ R p j v x (coreWeightOperator hO hD (besselWeight 2) F x) := by
  rw [Module.End.mul_apply,
    nativeB_firstNormalizedCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR,
    coreWeight_one_coefficientDerivative_nativeZ_apply hO hD hF g1 hg1 L lam δ R p hδ hR v F x]
  rfl

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
