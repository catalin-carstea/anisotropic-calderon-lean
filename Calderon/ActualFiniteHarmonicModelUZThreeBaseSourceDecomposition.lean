import Calderon.ActualFiniteHarmonicModelUZSecondBaseOperator
import Calderon.ActualFiniteHarmonicModelUZFirstBaseOperator
import Calderon.ActualFiniteHarmonicModelUZZeroBaseOperator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords
  SpectralWeightedGraph ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma nativeU_mul_nativeZ_eq_three_base_source
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR =
      nativeUZSecondBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR +
      nativeUZFirstBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR +
      nativeUZZeroBaseOperator hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  rw [nativeU_right_product_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  rfl

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
