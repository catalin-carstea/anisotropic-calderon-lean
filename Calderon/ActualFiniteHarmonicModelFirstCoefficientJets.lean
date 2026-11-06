import Calderon.ActualFiniteHarmonicModelFirstAngularJets

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelErrorAssembly
  ActualModelCommutatorWords ActualReferenceDDNormalizedCoefficient ActualReferenceDDHigherSpectralGraphs
  ActualPhysicalMixedFirst ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift
  ActualNormalizedSecondDriftWeightedCoefficients NaturalAngularAdjoint
  ReferenceDensityBounds NormalizedPrincipalMetric PrincipalCommutator ConformalDepth
  SmoothMetricFrame SmoothSphereFields SmoothAngularApplication
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeBFirstNormalizedFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeBFirstNormalizedFunction

lemma contDiff_modelFirstNormalizedCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) := by
  let h := referenceNormalizedPrincipalDifference g1 g2 L lam
  have hh : ContDiff ℝ ∞ h :=
    contDiff_referenceNormalizedPrincipalDifference g1 g2 hg1 hg2 L lam
  have hK := contDiff_referenceWeightedFirstBaseNormalizedCoefficient hO hD g1 hg1 L lam δ R p
    hδ hR h hh j
  have hm (a : Fin 3) : ContDiff ℝ ∞ (physicalMixedFirstCoefficient g1 L lam h a j) :=
    contDiff_physicalMixedFirstCoefficient g1 hg1 L lam h
      (fun i k => (contDiff_apply_apply ℝ ℝ i k).comp hh) a j
  have hJ := contDiff_normalizedSecondDriftFirstNormalizedCoefficient hO hD g1 g2 hg1 hg2
    L lam δ R p hδ hR j
  unfold modelFirstNormalizedCoefficient
  exact (hK.add (ContDiff.sum fun a _ => (hm a).smul contDiff_const)).add hJ

lemma nativeB_firstNormalizedCoefficient_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F x =
      modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  rfl

lemma coefficientDerivative_nativeB_firstNormalized_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) F x =
    directionalFDeriv v (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) x
      (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hact : (fun y => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F y) =
      (fun y => (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) y (U y)) :=
    funext (fun y => nativeB_firstNormalizedCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F y)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F y) x -
      nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,nativeB_firstNormalizedCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) (U : R3 → SphereL2)
    (contDiff_modelFirstNormalizedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) U.property.1 x,hW]
  abel

lemma coefficientDerivative_second_nativeB_firstNormalized_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (j : Fin 3) (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coefficientDerivative (coreDirectionalDerivative hO hD u)
        (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)) F x =
    directionalFDeriv v (directionalFDeriv u (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j)) x
      (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  let A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    coefficientDerivative (coreDirectionalDerivative hO hD u) (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      A G y = directionalFDeriv u (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) y
        (coreWeightOperator hO hD (besselWeight 1) G y) :=
    coefficientDerivative_nativeB_firstNormalized_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR u G y
  have hact : (fun y => A F y) =
      (fun y => directionalFDeriv u (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j) y (U y)) :=
    funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => A F y) x - A (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j))
    (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u _ (contDiff_modelFirstNormalizedCoefficient hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR))
    U.property.1 x,hW]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
