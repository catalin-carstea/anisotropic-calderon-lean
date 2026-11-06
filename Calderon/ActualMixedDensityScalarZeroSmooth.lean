import Calderon.ActualMixedDensityScalarZeroFormBase
import Calderon.FiniteScalarFieldSmoothness
import Calderon.ActualMixedDensityScalarZeroCoefficientSmooth

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ReferenceDensityBounds PrincipalCommutator ActualPhysicalMixedFirst ActualHorizontalNormBridge
  ActualReferenceDDHigherGeometryJets CoordinateBootstrapJets ActualMixedDensityHigherCoefficientJets
  ActualMixedDensityRaisingCoefficientJets ActualMixedDensityRemainderForm ActualMixedDensityRemainderProfile
  AmbientAngularShift BoundedAngularShift SpectralWeightedGraph SpectralWeightComparison SectionFiveErrorForms
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ConformalDepth RadiusProfile ReferenceWeightedApproximation

theorem contDiff_mixedDensityScalarZeroField
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (mixedDensityScalarZeroField hF hO hD g1 g2 L lam δ R p G hG) := by
  unfold mixedDensityScalarZeroField
  exact OAI.AnisotropicCalderon.FiniteScalarFieldSmoothness.contDiff_neg_triple_sum_smul
    (X := R3) (E := SphereL2)
    (fun i j a x => referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i j *
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
        (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a)) x)
    (fun a => ambientDerivativeField hF hO hD a G hG)
    (fun i j a => contDiff_mixedDensityScalarZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR i j a)
    (fun a => contDiff_ambientDerivativeField hF hO hD a G hG)

end OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
