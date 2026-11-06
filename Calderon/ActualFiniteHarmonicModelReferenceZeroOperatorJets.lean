import Calderon.ActualFiniteHarmonicModelReferenceZeroBalancedBounds
import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  BoundedAngularShift PrincipalCommutator ConformalDepth ReferenceDensityBounds
  SmoothSphereFields SmoothAngularApplication
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroOperatorJetFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroOperatorJetFunction

lemma nativeReferenceZeroDefect_scalarCentral
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    ScalarCentral hO hD (2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
      nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)) := by
  have hh := scalarCentral_sub hO hD
    (nativeH0 hO hD hF g g hg L lam δ R p hg hδ hR)
    (nativeW hO hD hF g g hg L lam δ R p hg hδ hR)
    (nativeH0_scalarCentral hO hD hF g g hg L lam δ R p hg hδ hR)
    (nativeW_scalarCentral hO hD hF g g hg L lam δ R p hg hδ hR)
  have he : nativeH0 hO hD hF g g hg L lam δ R p hg hδ hR -
      nativeW hO hD hF g g hg L lam δ R p hg hδ hR =
      2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
        nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR) := by
    unfold nativeH0
    abel
  rw [he] at hh
  exact hh

lemma coefficientDerivative_nativeReferenceZeroDefect_secondAngular_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
      nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)) F x =
      directionalFDeriv v (nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let N : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
      nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 2) F
  let A := nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      N G y = A y (coreWeightOperator hO hD (besselWeight 2) G y) :=
    nativeReferenceZeroDefect_secondAngularCoefficient_apply hO hD hF g hg L lam δ R p hδ hR G y
  have hact : (fun y => N F y) = (fun y => A y (U y)) := funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 2) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change directionalFDeriv v (fun y => N F y) x-N (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v A (U : R3 → SphereL2)
    (contDiff_nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p hδ hR)
    U.property.1 x,hW]
  abel

lemma coefficientDerivative_second_nativeReferenceZeroDefect_secondAngular_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coefficientDerivative (coreDirectionalDerivative hO hD u)
        (2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
      nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR))) F x =
      directionalFDeriv v (directionalFDeriv u
        (nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p)) x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let N : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
      nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 2) F
  let A := nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p
  let B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    coefficientDerivative (coreDirectionalDerivative hO hD u) N
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      B G y = directionalFDeriv u A y (coreWeightOperator hO hD (besselWeight 2) G y) :=
    coefficientDerivative_nativeReferenceZeroDefect_secondAngular_apply hO hD hF g hg
      L lam δ R p hδ hR u G y
  have hact : (fun y => B F y) = (fun y => directionalFDeriv u A y (U y)) := funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 2) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change directionalFDeriv v (fun y => B F y) x-B (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u A) (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u A
      (contDiff_nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p hδ hR))
    U.property.1 x,hW]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
