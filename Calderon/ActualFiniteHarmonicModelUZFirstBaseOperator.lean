import Calderon.ActualFiniteHarmonicModelNativeWords

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

def nativeUZFirstBaseOperator
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  firstBaseRightProduct
    (fun i => coreDirectionalDerivative hO hD (coordinateDirection i))
    (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR)
    (fun i => nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)
    (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)

lemma nativeUZFirstBaseOperator_eq_source
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    nativeUZFirstBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR =
      firstBaseRightProduct
        (fun i => coreDirectionalDerivative hO hD (coordinateDirection i))
        (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR)
        (fun i => nativeB hO hD hF g1 g2 hg1 L lam δ R p i hg2 hδ hR)
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) := by rfl

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
