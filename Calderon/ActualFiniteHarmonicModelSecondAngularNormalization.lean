import Calderon.ActualFiniteHarmonicModelShiftWeights
import Calderon.ActualFiniteHarmonicModelNativeCoefficients

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
private abbrev nativeWSecondFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWSecondFunction
def nativeWSecondAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x =>
    let h := referenceNormalizedPrincipalDifference g1 g2 L lam
    let I := inverseDegreeMultiplier hO hD
    let Id := ContinuousLinearMap.id ℝ SphereL2
    let mu := fun y : R3 => referenceDensityFamily g1 L (lam,y)
    let K0 := referenceWeightedZeroBaseNormalizedCoefficientTrace hO hD g1 hg1 L lam δ R p h
    (adjointZeroCoefficient coordinateDirection mu (actualPrincipalMatrix g1 L lam δ R p h) x) •
      (I.comp I) -
    (mu x)⁻¹ • ∑ j : Fin 3,
      (weightedAngularAdjointDerivative (coordinateDirection j) mu
        (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j) x).comp I +
    (ContinuousLinearMap.adjoint (K0 x) - K0 x) +
    (∑ a : Fin 3, physicalMixedDensityCorrection g1 L lam h a x •
      ((normalizedDerivative hF hO hD a).comp I)) +
    ((∑ a : Fin 3, physicalMixedProfileCoefficient g1 L lam δ R p h a x •
      ((normalizedDerivative hF hO hD a).comp (Id - (2 : ℝ) • I))) -
      (∑ a : Fin 3, physicalMixedProfileCoefficient g1 L lam δ R p h a x •
        ((normalizedRaising hF hO hD a).comp (Id - I)))) +
    ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      (-physicalMixedConnectionCoefficient g1 L lam h a b c x) •
        ((normalizedRotation hO hD b c).comp
          ((normalizedDerivative hF hO hD a).comp (Id - I)))) -
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        physicalMixedConnectionCoefficient g1 L lam h a b c x •
          ((normalizedRaising hF hO hD a).comp (normalizedRotation hO hD b c)))) +
    ((∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g1 L lam δ R p h a b x •
      ((normalizedDerivative hF hO hD b).comp
        ((normalizedDerivative hF hO hD a).comp (Id - I)))) -
      (∑ a : Fin 3, ∑ b : Fin 3, physicalPureAngularCoefficient g1 L lam δ R p h a b x •
        ((normalizedRaising hF hO hD a).comp
          ((normalizedRaising hF hO hD b).comp (Id + I))))) +
    (-2 : ℝ) • (referenceRadius δ R p L x • ∑ a : Fin 3,
      normalizedSecondDriftFrameJoint g1 g2 L a (lam,x) •
        ((1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3,
          referenceFrameConnectionCoefficient g1 L lam x
            (referenceMetricGramFrame g1 L (lam,x) a) b c •
              ((normalizedRotation hO hD b c).comp I))) -
    normalizedSecondDriftDensityDivergence g1 g2 L lam δ R p x • (I.comp I)

lemma nativeW_secondAngularCoefficient_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x =
      nativeWSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
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
  have hDC (a b c : Fin 3) : coreRotation hO hD b c (coreDerivative hO hD hF a F) x =
      normalizedRotation hO hD b c (normalizedDerivative hF hO hD a (V-U)) := by
    rw [coreRotation_apply_eq_normalizedRotation hO hD b c (coreDerivative hO hD hF a F) x,
      coreWeight_one_derivative_apply_eq_normalized_shift hO hD hF a F x]
  have hRC (a b c : Fin 3) : coreRaising hO hD hF a (coreRotation hO hD b c F) x =
      normalizedRaising hF hO hD a (normalizedRotation hO hD b c V) := by
    change normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) (coreRotation hO hD b c F) x) = _
    rw [hRotW b c]
  have hDD (a b : Fin 3) : normalizedDerivative hF hO hD b
      (coreWeightOperator hO hD (besselWeight 1) (coreDerivative hO hD hF a F) x) =
      normalizedDerivative hF hO hD b (normalizedDerivative hF hO hD a (V-U)) := by
    rw [coreWeight_one_derivative_apply_eq_normalized_shift hO hD hF a F x]
  have hRR (a b : Fin 3) : normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) (coreRaising hO hD hF b F) x) =
      normalizedRaising hF hO hD a (normalizedRaising hF hO hD b (V+U)) := by
    rw [coreWeight_one_raising_apply_eq_normalized_shift hO hD hF b F x]
  have hi2Explicit : inverseDegreeMultiplier hO hD
      (coreWeightOperator hO hD (besselWeight 2) F x) =
      coreWeightOperator hO hD (besselWeight 1) F x := by
    simpa only [I,V,U] using hi2
  have hi1Explicit : inverseDegreeMultiplier hO hD
      (coreWeightOperator hO hD (besselWeight 1) F x) = F x := by
    simpa only [I,U] using hi1
  have hdExplicit (a : Fin 3) : normalizedDerivative hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x) = coreDerivative hO hD hF a F x := by
    simpa only [U] using hd a
  have hrotExplicit (b c : Fin 3) : normalizedRotation hO hD b c
      (coreWeightOperator hO hD (besselWeight 1) F x) = coreRotation hO hD b c F x := by
    simpa only [U] using hrot b c
  rw [nativeW_eq_coreModelDefectZero hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  unfold coreModelDefectZeroCoefficientAction
  dsimp only
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,LinearMap.sum_apply,coreScalar,coreCoefficientAction,
    coreNormalizedDerivative,coreNormalizedRaising,LinearMap.coe_mk,AddHom.coe_mk,
    Submodule.coe_mk,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,Submodule.coe_sum,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply]
  simp_rw [hDC,hRC,hDD,hRR]
  unfold nativeWSecondAngularCoefficient
  dsimp only
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,hi2Explicit,hi1Explicit,hdExplicit,hrotExplicit]
  simp only [U,V]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
