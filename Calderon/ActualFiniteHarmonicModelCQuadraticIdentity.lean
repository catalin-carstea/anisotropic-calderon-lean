import Calderon.ActualFiniteHarmonicModelZeroAngularNormalization
import Calderon.ActualFiniteHarmonicModelReferenceTraceZeroRaw
import Calderon.ActualFiniteHarmonicModelDriftZeroRaw

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
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
private abbrev nativeCQuadraticFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeCQuadraticFunction
lemma nativeC_eq_raw_quadratic_coefficients
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR =
    nativeReferenceTraceZeroRawAction hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam)
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR +
    (∑ a : Fin 3, coreScalar hO hD
      (physicalMixedProfileCoefficient g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) a)
      (contDiff_physicalMixedProfileCoefficient g1 hg1 L lam δ R p _ hδ hR
        (fun i j => NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j) a)*
      (coreRaising hO hD hF a*coreDegree hO hD)) +
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, coreScalar hO hD
      (physicalMixedConnectionCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a b c)
      (contDiff_physicalMixedConnectionCoefficient g1 hg1 L lam _
        (fun i j => NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j) a b c)*
      (coreRaising hO hD hF a*coreRotation hO hD b c)) +
    (∑ a : Fin 3, ∑ b : Fin 3, coreScalar hO hD
      (physicalPureAngularCoefficient g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) a b)
      (contDiff_physicalPureAngularCoefficient g1 hg1 L lam δ R p _ hδ hR
        (fun i j => NormalizedPrincipalMetricSmooth.contDiff_referenceNormalizedPrincipalDifference_entry g1 g2 hg1 hg2 L lam i j) a b)*
      (coreRaising hO hD hF a*coreRaising hO hD hF b)) +
    nativeDriftZeroRawAction hO hD g1 g2 hg1 hg2 L lam δ R p hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  let I := inverseDegreeMultiplier hO hD
  let U : SphereL2 := coreWeightOperator hO hD (besselWeight 1) F x
  let V : SphereL2 := coreWeightOperator hO hD (besselWeight 2) F x
  have hUV : (U,V) ∈ sphereBesselGraph hO hD 1 := by
    change (coreWeightOperator hO hD (besselWeight 1) F x,
      coreWeightOperator hO hD (besselWeight 2) F x) ∈ sphereBesselGraph hO hD 1
    rw [← coreWeight_one_twice_apply hO hD F x]
    exact coreWeightOperator_graph hO hD (besselWeight 1)
      (coreWeightOperator hO hD (besselWeight 1) F) x
  have hi2 : I V = U := inverseDegreeMultiplier_of_besselGraph hO hD U V hUV
  have hi1 : I U = F x := inverseDegreeMultiplier_of_besselGraph hO hD _ _
    (coreWeightOperator_graph hO hD (besselWeight 1) F x)
  have hd (a : Fin 3) : normalizedDerivative hF hO hD a U = coreDerivative hO hD hF a F x := rfl
  have hrot (b c : Fin 3) : normalizedRotation hO hD b c U = coreRotation hO hD b c F x :=
    (coreRotation_apply_eq_normalizedRotation hO hD b c F x).symm
  have hRotW (b c : Fin 3) :
      coreWeightOperator hO hD (besselWeight 1) (coreRotation hO hD b c F) x =
        normalizedRotation hO hD b c V := by
    have ha := preservesSphereSpectralGraphs_normalizedRotation hO hD b c
      (besselWeight 1) U V hUV
    have hw := coreWeightOperator_graph hO hD (besselWeight 1) (coreRotation hO hD b c F) x
    rw [coreRotation_apply_eq_normalizedRotation hO hD b c F x] at hw
    exact spectralGraph_output_unique hO hD (besselWeight 1)
      (normalizedRotation hO hD b c U) _ _ hw ha
  have hRC (a b c : Fin 3) : coreRaising hO hD hF a (coreRotation hO hD b c F) x =
      normalizedRaising hF hO hD a (normalizedRotation hO hD b c V) := by
    change normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) (coreRotation hO hD b c F) x) = _
    rw [hRotW b c]
  have hRR (a b : Fin 3) : normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF b F) x) =
      normalizedRaising hF hO hD a (normalizedRaising hF hO hD b (V+U)) := by
    rw [coreWeight_one_raising_apply_eq_normalized_shift hO hD hF b F x]
  have hRN (a : Fin 3) : coreRaising hO hD hF a (coreDegree hO hD F) x =
      normalizedRaising hF hO hD a (V-U) := by
    change normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 1) (coreDegree hO hD F) x) = _
    rw [coreWeight_one_degree_apply hO hD F x]
  have hRRraw (a b : Fin 3) : coreRaising hO hD hF a (coreRaising hO hD hF b F) x =
      normalizedRaising hF hO hD a (normalizedRaising hF hO hD b (V+U)) := hRR a b
  dsimp only [V,U,I] at hi2 hRN hRC hRRraw
  rw [nativeC_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x]
  simp only [LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,Submodule.coe_add,
    Submodule.coe_sum,Pi.add_apply,Finset.sum_apply]
  rw [nativeReferenceTraceZeroRawAction_apply,nativeDriftZeroRawAction_apply]
  simp only [coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]
  change nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p x V = _
  unfold nativeCSecondAngularCoefficient
  dsimp only
  simp only [V,U,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    hi2,hRN,hRC,hRRraw]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
