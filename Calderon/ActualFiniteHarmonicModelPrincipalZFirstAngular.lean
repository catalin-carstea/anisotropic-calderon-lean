import Calderon.ActualFiniteHarmonicModelPrincipalHWordsBounds
import Calderon.ActualFiniteHarmonicModelReferenceDefectCoefficientDerivative

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric PrincipalCommutator ReferenceDensityBounds ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativePrincipalZFirstAngularFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativePrincipalZFirstAngularFunction

def nativePrincipalZFirstAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ)
    (i j : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) x i j •
      nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g1 L lam δ R p x

lemma nativePrincipalCoefficient_nativeZ_firstAngular_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ)
    (i j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x =
      nativePrincipalZFirstAngularCoefficient hO hD hF g1 g2 hg1
        L lam δ R p i j x (coreWeightOperator hO hD (besselWeight 1) F x) := by
  rw [Module.End.mul_apply,
    nativePrincipalCoefficient_apply_eq_actualPrincipal hO hD g1 g2 hg1
      L lam δ R p hg2 hδ hR i j,
    nativeZ_firstNormalizedCoefficient_apply hO hD hF g1 hg1
      L lam δ R p hδ hR F x]
  rfl

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
