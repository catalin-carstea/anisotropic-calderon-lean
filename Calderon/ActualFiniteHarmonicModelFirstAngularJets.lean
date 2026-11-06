import Calderon.ActualFiniteHarmonicModelFirstAngularNormalization
import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualModelCommutatorWords ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftWeightedCoefficients NaturalAngularAdjoint
  ReferenceDensityBounds NormalizedPrincipalMetric PrincipalCommutator ConformalDepth
  SmoothMetricFrame SmoothSphereFields SmoothAngularApplication
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev firstAngularJetFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] firstAngularJetFunction

def nativeHFirstAngularCoefficient (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => (∑ a : Fin 3,
    (-2 * referenceMetricGramFrame g1 L (lam,x) a j -
      physicalMixedFirstCoefficient g1 L lam (referenceNormalizedPrincipalDifference g1 g2 L lam) a j x) •
      (normalizedDerivative hF hO hD a + normalizedRaising hF hO hD a)) -
    (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x +
      ContinuousLinearMap.adjoint (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x)) +
    (adjointFirstCoefficient coordinateDirection (fun y => referenceDensityFamily g1 L (lam,y))
        (actualPrincipalMatrix g1 L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam)) x j -
      2 * (referenceRadius δ R p L x * normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x))) •
      inverseDegreeMultiplier hO hD

lemma contDiff_nativeHFirstAngularCoefficient (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) := by
  have hh := ActualNormalizedSecondModelErrorAssembly.contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have he (a : Fin 3) : ContDiff ℝ ∞
      (fun x => referenceMetricGramFrame g1 L (lam,x) a j) :=
    ((contDiff_piLp_apply (p := 2) (i := j) : ContDiff ℝ ∞ (fun v : R3 => v j)).comp
      (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a))
  have hm (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g1 L lam
      (referenceNormalizedPrincipalDifference g1 g2 L lam) a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam _
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  have hK := contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    hδ hR (referenceNormalizedPrincipalDifference g1 g2 L lam) hh j
  have hKa : ContDiff ℝ ∞ (fun x => ContinuousLinearMap.adjoint
      (referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
        (referenceNormalizedPrincipalDifference g1 g2 L lam) j x)) :=
    contDiff_angularAdjoint _ hK
  have ha := contDiff_modelAdjointFirstCoefficient g1 g2 hg1 hg2 L lam δ R p hδ hR j
  have hr := contDiff_referenceRadius_actual δ R p L hδ hR
  have hb : ContDiff ℝ ∞ (fun x : R3 => normalizedSecondDriftCoordinateJoint g1 g2 L j (lam,x)) :=
    (contDiff_normalizedSecondDriftCoordinateJoint g1 g2 hg1 hg2 L j).comp
      (contDiff_const.prodMk contDiff_id)
  unfold nativeHFirstAngularCoefficient
  exact ((ContDiff.sum fun a _ => (((contDiff_const.mul (he a)).sub (hm a)).smul
    contDiff_const)).sub (hK.add hKa)).add
      ((ha.sub (contDiff_const.mul (hr.mul hb))).smul contDiff_const)

lemma nativeH_firstAngularCoefficient_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x =
      (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x (coreWeightOperator hO hD (besselWeight 1) F x) := by
  have hd (a : Fin 3) : normalizedDerivative hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x) = coreDerivative hO hD hF a F x := rfl
  have hr (a : Fin 3) : normalizedRaising hF hO hD a
      (coreWeightOperator hO hD (besselWeight 1) F x) = coreRaising hO hD hF a F x := rfl
  rw [nativeH_apply_eq_firstAngularField hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F x]
  unfold nativeHFirstAngularField nativeHFirstAngularCoefficient
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,hd,hr,
    inverseDegreeMultiplier_coreWeight_one_apply hO hD F x]

lemma coefficientDerivative_nativeH_firstAngular_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) F x =
    directionalFDeriv v (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) x
      (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hact : (fun y => nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F y) =
      (fun y => (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) y (U y)) :=
    funext (fun y => nativeH_firstAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F y)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j F y) x -
      nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,nativeH_firstAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) (U : R3 → SphereL2)
    (contDiff_nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) U.property.1 x,hW]
  abel

lemma coefficientDerivative_second_nativeH_firstAngular_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coefficientDerivative (coreDirectionalDerivative hO hD u)
        (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j)) F x =
    directionalFDeriv v (directionalFDeriv u (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j)) x
      (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  let A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    coefficientDerivative (coreDirectionalDerivative hO hD u) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j)
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      A G y = directionalFDeriv u (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) y
        (coreWeightOperator hO hD (besselWeight 1) G y) :=
    coefficientDerivative_nativeH_firstAngular_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR u G y
  have hact : (fun y => A F y) =
      (fun y => directionalFDeriv u (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j) y (U y)) :=
    funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => A F y) x - A (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u (nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j))
    (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u _ (contDiff_nativeHFirstAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR))
    U.property.1 x,hW]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
