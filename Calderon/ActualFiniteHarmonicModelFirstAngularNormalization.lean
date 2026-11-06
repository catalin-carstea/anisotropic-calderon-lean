import Calderon.ActualFiniteHarmonicModelFirstDefect
import Calderon.ActualFirstAngularCoefficientAlgebra

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph BoundedAngularShift ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients
  ActualScalarPrincipalAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothSphereFields SmoothAngularApplication
  ActualModelCommutatorWords ActualPhysicalMixedFirst ActualReferenceDDNormalizedCoefficient
  ActualNormalizedSecondDriftAngularAllocation ActualNormalizedSecondMetricDrift SmoothMetricFrame MovingFrameConnection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularNormalizationFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularNormalizationFunction

def nativeHFirstAngularField (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  fun x => (∑ a : Fin 3,
    (-2 * referenceMetricGramFrame g1 L (lam,x) a j - physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x) •
      (coreDerivative hO hD hF a F x + coreRaising hO hD hF a F x)) -
    ((referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) j x) + ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) j x))
      (coreWeightOperator hO hD (besselWeight 1) F x) +
    ((adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j) - 2 * (referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))) • F x

lemma inverseDegreeMultiplier_coreWeight_one_apply (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight 1) F x) = F x := by
  exact inverseDegreeMultiplier_of_besselGraph hO hD (F x)
    (coreWeightOperator hO hD (besselWeight 1) F x)
    (coreWeightOperator_graph hO hD (besselWeight 1) F x)

lemma nativeV_firstAngular_action (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      (adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j) • F x -
      ((referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) j x) + ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) j x))
        (coreWeightOperator hO hD (besselWeight 1) F x) -
      (∑ a : Fin 3, physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x • (coreDerivative hO hD hF a F x + coreRaising hO hD hF a F x)) -
      (2 * (referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))) • F x := by
  have hd (a : Fin 3) : normalizedDerivative hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x) = coreDerivative hO hD hF a F x := rfl
  have hr (a : Fin 3) : normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x) = coreRaising hO hD hF a F x := rfl
  change modelDefectFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
    (coreWeightOperator hO hD (besselWeight 1) F x) = _
  simp only [modelDefectFirstNormalizedCoefficient, normalizedSecondDriftFirstNormalizedCoefficient,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inverseDegreeMultiplier_coreWeight_one_apply hO hD F x,
    hd, hr, smul_smul, sub_add_eq_sub_sub, mul_assoc]

lemma nativeH_apply_eq_firstAngularField (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x = nativeHFirstAngularField hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x := by
  have ht : nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j F x =
      ∑ a : Fin 3, referenceMetricGramFrame g1 L (lam,x) a j • coreRaising hO hD hF a F x := by
    simp only [nativeReferenceFirstCoefficient, LinearMap.sum_apply, Module.End.mul_apply,
      Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a ha
    have hce : Commute (coreRaising hO hD hF a)
        (nativeReferenceFrameScalar hO hD g1 hg1 L lam a j) := by
      unfold nativeReferenceFrameScalar
      exact scalarCentral_coreRaising hO hD hF a _ _
    exact congrArg
      (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) hce.eq
  have htd : nativeReferenceAdjointFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j F x =
      -(∑ a : Fin 3, referenceMetricGramFrame g1 L (lam,x) a j • coreDerivative hO hD hF a F x) := by
    simp only [nativeReferenceAdjointFirstCoefficient, LinearMap.sum_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, neg_one_smul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have hce : Commute (coreDerivative hO hD hF a)
        (nativeReferenceFrameScalar hO hD g1 hg1 L lam a j) := by
      unfold nativeReferenceFrameScalar
      exact scalarCentral_coreDerivative hO hD hF a _ _
    exact congrArg (fun y : SphereL2 => -y)
      (congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x) hce.eq)
  simp only [nativeH, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.ofNat_apply, two_nsmul, Submodule.coe_add, Submodule.coe_sub,
    Pi.add_apply, Pi.sub_apply]
  rw [ht, htd, nativeV_firstAngular_action hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x]
  unfold nativeHFirstAngularField
  exact ActualFirstAngularCoefficientAlgebra.firstAngularCoefficient_collection
    (fun a => referenceMetricGramFrame g1 L (lam,x) a j)
    (fun a => physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x)
    (fun a => coreDerivative hO hD hF a F x)
    (fun a => coreRaising hO hD hF a F x)
    ((referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) j x +
      ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x))
      (coreWeightOperator hO hD (besselWeight 1) F x))
    (F x)
    (adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
      (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j)
    (referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
