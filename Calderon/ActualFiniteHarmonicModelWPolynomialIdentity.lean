import Calderon.ActualFiniteHarmonicModelWPolynomialPart
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
private abbrev nativeWPolynomialIdentityFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWPolynomialIdentityFunction
lemma nativeW_eq_polynomial_and_density_parts
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR =
    coreScalar hO hD
      (fun x => adjointZeroCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x)
      (contDiff_modelAdjointZeroCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR) +
    nativeReferenceWeightedAdjointDerivativeRawAction hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam)
      (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR +
    nativeWPolynomialPart hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR -
    coreScalar hO hD (normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p)
      (contDiff_normalizedSecondDriftDensityDivergence g1 g2 hg1 hg2 L lam δ R p hδ hR) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hDN (a : Fin 3) : coreDerivative hO hD hF a (coreDegree hO hD F-F) x =
      normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x-
        (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1) F x) := by
    have hw : coreWeightOperator hO hD (besselWeight 1) (coreDegree hO hD F-F) x =
        coreWeightOperator hO hD (besselWeight 2) F x-(2 : ℝ) • coreWeightOperator hO hD (besselWeight 1) F x := by
      have hm := congrArg (fun G : smoothCompactFiniteSphereCore hO hD => G x)
        (map_sub (coreWeightOperator hO hD (besselWeight 1)) (coreDegree hO hD F) F)
      rw [hm]
      change coreWeightOperator hO hD (besselWeight 1) (coreDegree hO hD F) x-
        coreWeightOperator hO hD (besselWeight 1) F x = _
      rw [coreWeight_one_degree_apply hO hD F x]
      module
    change normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 1) (coreDegree hO hD F-F) x)=_
    rw [hw]
  have hRN (a : Fin 3) : coreRaising hO hD hF a (coreDegree hO hD F) x =
      normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 2) F x-
        coreWeightOperator hO hD (besselWeight 1) F x) := by
    change normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 1) (coreDegree hO hD F) x)=_
    rw [coreWeight_one_degree_apply hO hD F x]
  rw [nativeW_eq_coreModelDefectZero]
  unfold coreModelDefectZeroCoefficientAction nativeWPolynomialPart
  dsimp only
  simp only [Module.End.mul_apply,Module.End.one_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sum_apply,coreScalar,coreCoefficientAction,
    coreNormalizedDerivative,coreNormalizedRaising,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_smul,
    Submodule.coe_sum,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,hDN,hRN]
  rw [nativeReferenceTraceZeroRawAction_apply]
  simp_rw [weightedAngularAdjointDerivative_referenceWeightedFirst_coreWeight_one_apply hO hD g1 hg1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam)
    (ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam) hδ hR]
  unfold nativeReferenceTraceZeroAdjointRawAction nativeDriftConnectionRawAction
    nativeReferenceWeightedAdjointDerivativeRawAction nativeReferenceConnectionAction
  dsimp only
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,
    LinearMap.smul_apply,LinearMap.sum_apply,coreScalar,coreCoefficientAction,
    coreNormalizedDerivative,coreNormalizedRaising,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_neg,Submodule.coe_smul,Submodule.coe_sum,
    Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,Finset.sum_apply,hDN,hRN]
  have hd (a : Fin 3) (G : smoothCompactFiniteSphereCore hO hD) :
      normalizedDerivative hF hO hD a (coreWeightOperator hO hD (besselWeight 1) G x)=coreDerivative hO hD hF a G x := rfl
  have hr (a : Fin 3) (G : smoothCompactFiniteSphereCore hO hD) :
      normalizedRaising hF hO hD a (coreWeightOperator hO hD (besselWeight 1) G x)=coreRaising hO hD hF a G x := rfl
  simp only [hd,hr,smul_sub,smul_neg,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.smul_sum,
    neg_smul,smul_smul,neg_one_mul,Finset.sum_neg_distrib]
  trace_state
  module

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
