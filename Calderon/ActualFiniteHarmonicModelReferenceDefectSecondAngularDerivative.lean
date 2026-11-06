import Calderon.ActualFiniteHarmonicModelBZSecondAngularBounds
import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualModelCommutatorWords PrincipalCommutator
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeZSecondAngularDerivativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeZSecondAngularDerivativeFunction

lemma coreWeight_one_coefficientDerivative_nativeZ_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1)
      (coefficientDerivative (coreDirectionalDerivative hO hD v)
        (nativeZ hO hD hF g hg L lam δ R p hδ hR) F) x =
      directionalFDeriv v
        (nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p) x
          (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let W1 := coreWeightOperator hO hD (besselWeight 1)
  let W2 := coreWeightOperator hO hD (besselWeight 2)
  let d := coreDirectionalDerivative hO hD v
  let Z := nativeZ hO hD hF g hg L lam δ R p hδ hR
  let A := nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p
  have hact : (fun y => W1 (Z F) y) = (fun y => A y (W2 F y)) :=
    funext (fun y => coreWeight_one_nativeZ_apply hO hD hF g hg L lam δ R p hδ hR F y)
  have hW1 : W1 (d (Z F)) x = directionalFDeriv v (W1 (Z F) : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T (Z F) x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  have hW2 : W2 (d F) x = directionalFDeriv v (W2 F : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change W1 (d (Z F) - Z (d F)) x = _
  rw [map_sub]
  change W1 (d (Z F)) x - W1 (Z (d F)) x = _
  rw [hW1,coreWeight_one_nativeZ_apply hO hD hF g hg L lam δ R p hδ hR (d F) x]
  change directionalFDeriv v (fun y => W1 (Z F) y) x - A x (W2 (d F) x) = _
  rw [hact,hW2]
  rw [directionalFDeriv_clm_apply v A (W2 F : R3 → SphereL2)
    (contDiff_nativeReferenceDefectSecondAngularCoefficient hO hD hF g hg L lam δ R p hδ hR)
    (W2 F).property.1 x]
  abel

lemma coreWeight_one_coefficientDerivative_second_nativeZ_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1)
      (coefficientDerivative (coreDirectionalDerivative hO hD v)
        (coefficientDerivative (coreDirectionalDerivative hO hD u)
          (nativeZ hO hD hF g hg L lam δ R p hδ hR)) F) x =
      directionalFDeriv v (directionalFDeriv u
        (nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p)) x
          (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let W1 := coreWeightOperator hO hD (besselWeight 1)
  let W2 := coreWeightOperator hO hD (besselWeight 2)
  let d := coreDirectionalDerivative hO hD v
  let Z := nativeZ hO hD hF g hg L lam δ R p hδ hR
  let A := coefficientDerivative (coreDirectionalDerivative hO hD u) Z
  let B := nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      W1 (A G) y = directionalFDeriv u B y (W2 G y) :=
    coreWeight_one_coefficientDerivative_nativeZ_apply hO hD hF g hg L lam δ R p hδ hR u G y
  have hact : (fun y => W1 (A F) y) =
      (fun y => directionalFDeriv u B y (W2 F y)) := funext (ha F)
  have hW1 : W1 (d (A F)) x = directionalFDeriv v (W1 (A F) : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T (A F) x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  have hW2 : W2 (d F) x = directionalFDeriv v (W2 F : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 2) v).eq
  change W1 (d (A F) - A (d F)) x = _
  rw [map_sub]
  change W1 (d (A F)) x - W1 (A (d F)) x = _
  rw [hW1,ha (d F) x]
  change directionalFDeriv v (fun y => W1 (A F) y) x -
      directionalFDeriv u B x (W2 (d F) x) = _
  rw [hact,hW2]
  rw [directionalFDeriv_clm_apply v (directionalFDeriv u B)
    (W2 F : R3 → SphereL2)
    (contDiff_directionalFDeriv u _
      (contDiff_nativeReferenceDefectSecondAngularCoefficient hO hD hF g hg L lam δ R p hδ hR))
    (W2 F).property.1 x]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
