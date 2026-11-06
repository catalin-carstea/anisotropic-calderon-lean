import Calderon.ActualNormalizedSecondModelErrorAssembly

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualNormalizedSecondModelDefectNormalForm
open SphereHarmonic SphereHilbertDecomposition SmoothSphereFields SmoothAngularApplication
  ActualNormalizedSecondModelErrorAssembly ActualReferenceDDNativeAdjunction
  ActualReferenceOrdinaryPrincipal ActualScalarPrincipalAdjoint ActualPerturbedDefect
  ActualPhysicalMixedFirst ActualPhysicalMixedProfile ActualPhysicalMixedConnection
  ActualPhysicalPureAngular ActualNormalizedSecondDriftAngularAllocation
  ActualNormalizedSecondDriftNativeAdjunction NormalizedPrincipalMetric
  NormalizedPrincipalMetricSmooth PrincipalCommutator ReferenceDensityBounds
  ScalarBaseAdjoint ConformalDepth RadiusProfile

theorem normalizedSecondModelErrorDefect_normal_form
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    normalizedSecondModelErrorDefect hF hO hD g1 g2 hg1 L lam δ R p G hG x =
      adjointZeroCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x •
        ambientSphereL2 G hG x +
      (∑ i : Fin 3, adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x i •
        directionalFDeriv (coordinateDirection i) (ambientSphereL2 G hG) x) +
      (referenceWeightedFirstBaseAdjoint hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x -
        referenceWeightedFirstBaseTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x) +
      (referenceWeightedZeroBaseAdjoint hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x -
        referenceWeightedZeroBaseTrace hO hD g1 hg1 L lam δ R p
          (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x) +
      physicalMixedFirstDefect hF hO hD g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedProfileDefect hF hO hD g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalMixedConnectionDefect hF hO hD g1 L lam
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      physicalPureAngularDefect hF hO hD g1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) G hG x +
      (-2 : ℝ) • normalizedSecondDriftFirstBaseField hO hD g1 g2 hg1 L lam δ R p G hG x +
      (-2 : ℝ) • normalizedSecondDriftAngularConnectionField hO hD g1 g2 hg1 L lam δ R p G hG x -
      normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x • ambientSphereL2 G hG x := by
  rw [normalizedSecondModelErrorDefect_decomposition,
    referenceWeightedCovectorTraceDefect_normal_form hO hD g1 hg1 L lam δ R p hδ hR,
    actual_scalar_adjoint_defect g1 hg1 L lam δ R p _ (ambientSphereL2 G hG) hδ hR
      (fun i j => contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j)
      (contDiff_ambientSphereL2 G hG) x
      (Filter.Eventually.of_forall fun y => referenceNormalizedPrincipalDifference_isHermitian g1 g2 hg1 hg2 L lam y),
    normalizedSecondWeightedDriftAdjointDefect_normal_form hO hD g1 g2 hg1 L lam δ R p G hG hg2 hδ hR x]
  abel

end OAI.AnisotropicCalderon.ActualNormalizedSecondModelDefectNormalForm
