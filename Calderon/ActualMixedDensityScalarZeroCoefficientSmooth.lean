import Calderon.ActualMixedDensityScalarZeroFormBase
import Calderon.ActualMixedDensityScalarZeroFactorSmoothness

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


theorem contDiff_mixedDensityScalarZeroCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (i j a : Fin 3) :
    ContDiff ℝ ∞ (fun x : R3 =>
      referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i j *
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j)
          (physicalMixedDensityCorrection g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a)) x) := by
  exact (contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
    g1 g2 hg1 hg2 L lam δ R p hδ hR i j).mul
      (contDiff_physicalMixedDensityCorrection_second_actual g1 g2 hg1 hg2 L lam i j a)

end OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm
