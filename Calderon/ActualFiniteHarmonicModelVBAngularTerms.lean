import Calderon.ActualFiniteHarmonicModelConnectionSymmetric
import Calderon.ActualFiniteHarmonicModelBCLocality
import Calderon.ActualFiniteHarmonicModelNativeCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceDDNormalizedCoefficient ActualReferenceDDSpectralTransport ActualReferenceParallelRaising
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondMetricDrift ActualPhysicalMixedFirst
  ActualPhysicalMixedReferenceCancellation ActualScalarPrincipalAdjoint NaturalAngularAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothMetricFrame MovingFrameConnection AmbientReferenceRaising
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeVBAngularTermsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeVBAngularTermsFunction
lemma nativeB_apply_eq_full_angular_terms
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let h := referenceNormalizedPrincipalDifference g1 g2 L lam
    let r := referenceRadius δ R p L x
    let q := fun a b : Fin 3 => physicalMixedQFrameCoefficient g1 L lam h a b x
    let e := fun a : Fin 3 => referenceMetricGramFrame g1 L (lam,x) a j
    let A := fun a : Fin 3 => normalizedReferenceAngularConnection hO hD g1 L lam x
      (referenceMetricGramFrame g1 L (lam,x) a)
    let gamma := fun a b : Fin 3 => (referenceConnectionFamily g1 L (lam,x)
      (referenceMetricGramFrame g1 L (lam,x) a) (referenceMetricGramFrame g1 L (lam,x) b)) j
    let eta := fun a b : Fin 3 =>
      referenceFrameDerivative g1 L lam b (fun y => Real.log (referenceRadius δ R p L y)) x * e a +
        referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x * e b
    let m := fun a : Fin 3 => physicalMixedFirstCoefficient g1 L lam h a j x
    nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      r • ∑ a : Fin 3, ∑ b : Fin 3, q a b •
        ((-gamma a b) • F x + e a • A b (coreWeightOperator hO hD (besselWeight 1) F x) +
          e b • A a (coreWeightOperator hO hD (besselWeight 1) F x) +
          eta a b • coreDegree hO hD F x) +
      (∑ a : Fin 3, m a • coreRaising hO hD hF a F x) +
      (r * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) • F x := by
  dsimp only
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let w := coreWeightOperator hO hD (besselWeight 1) F x
  have hi : inverseDegreeMultiplier hO hD w = F x :=
    inverseDegreeMultiplier_of_besselGraph hO hD _ _ (coreWeightOperator_graph hO hD (besselWeight 1) F x)
  have hd : w-F x=coreDegree hO hD F x := coreWeight_one_sub_self_eq_degree hO hD F x
  have hder (a : Fin 3) : normalizedDerivative hF hO hD a w=coreDerivative hO hD hF a F x := rfl
  have hraise (a : Fin 3) : normalizedRaising hF hO hD a w=coreRaising hO hD hF a F x := rfl
  change modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x w = _
  unfold modelFirstNormalizedCoefficient referenceWeightedFirstBaseNormalizedCoefficient
    normalizedSecondDriftFirstNormalizedCoefficient
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.id_apply,hi,hd,hraise,smul_smul]
  rfl


lemma nativeV_apply_eq_full_angular_terms
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    let h := referenceNormalizedPrincipalDifference g1 g2 L lam
    let r := referenceRadius δ R p L x
    let q := fun a b : Fin 3 => physicalMixedQFrameCoefficient g1 L lam h a b x
    let e := fun a : Fin 3 => referenceMetricGramFrame g1 L (lam,x) a j
    let A := fun a : Fin 3 => normalizedReferenceAngularConnection hO hD g1 L lam x
      (referenceMetricGramFrame g1 L (lam,x) a)
    let gamma := fun a b : Fin 3 => (referenceConnectionFamily g1 L (lam,x)
      (referenceMetricGramFrame g1 L (lam,x) a) (referenceMetricGramFrame g1 L (lam,x) b)) j
    let eta := fun a b : Fin 3 =>
      referenceFrameDerivative g1 L lam b (fun y => Real.log (referenceRadius δ R p L y)) x * e a +
        referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)) x * e b
    let m := fun a : Fin 3 => physicalMixedFirstCoefficient g1 L lam h a j x
    nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p h) x j • F x -
      (2*r) • ∑ a : Fin 3, ∑ b : Fin 3, q a b •
        ((-gamma a b) • F x + eta a b • coreDegree hO hD F x) -
      (∑ a : Fin 3, m a • (coreDerivative hO hD hF a F x+coreRaising hO hD hF a F x)) -
      (2*r*normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) • F x := by
  dsimp only
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  let w := coreWeightOperator hO hD (besselWeight 1) F x
  have hi : inverseDegreeMultiplier hO hD w = F x :=
    inverseDegreeMultiplier_of_besselGraph hO hD _ _ (coreWeightOperator_graph hO hD (besselWeight 1) F x)
  have hd : w-F x=coreDegree hO hD F x := coreWeight_one_sub_self_eq_degree hO hD F x
  have hder (a : Fin 3) : normalizedDerivative hF hO hD a w=coreDerivative hO hD hF a F x := rfl
  have hraise (a : Fin 3) : normalizedRaising hF hO hD a w=coreRaising hO hD hF a F x := rfl
  let K := referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p h j x
  let a1 := adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
    (actualPrincipalMatrix g1 L lam δ R p h) x j
  have hK := nativeReferenceFirst_symmetric_coreWeight_action hO hD g1 g2 hg1 L lam δ R p j F x
  simp only [ContinuousLinearMap.add_apply] at hK
  change modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x w = _
  unfold modelDefectFirstNormalizedCoefficient normalizedSecondDriftFirstNormalizedCoefficient
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,hi,hder,hraise,smul_smul,mul_assoc]
  rw [sub_sub (a1 • F x) (K w) (ContinuousLinearMap.adjoint K w),hK]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
