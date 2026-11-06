import Calderon.ActualFiniteHarmonicModelThirdDerivativeShift
import Calderon.ActualFiniteHarmonicModelZeroAngularNormalization
import Calderon.ActualFiniteHarmonicModelReferenceDefectFirstNormalized
import Calderon.ActualFiniteHarmonicCoreScalarCentral

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeCZThirdFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeCZThirdFunction
def nativeCZThirdAngularCoefficient
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => (nativeCSecondAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p x).comp
    (∑ a : Fin 3,
      referenceFrameDerivative g1 L lam a
        (fun y => Real.log (referenceRadius δ R p L y)) x •
        ((normalizedDerivative hF hO hD a).comp
          ((ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD).comp
            (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD))))

lemma nativeCZ_thirdAngularCoefficient_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x =
      nativeCZThirdAngularCoefficient hO hD hF g1 g2 hg1 L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 3) F x) := by
  let W2 := coreWeightOperator hO hD (besselWeight 2)
  let W3 := coreWeightOperator hO hD (besselWeight 3)
  let I := inverseDegreeMultiplier hO hD
  let Id := ContinuousLinearMap.id ℝ SphereL2
  let T := (Id-I).comp (Id-I)
  let f (a : Fin 3) : R3 → ℝ := referenceFrameDerivative g1 L lam a
    (fun y => Real.log (referenceRadius δ R p L y))
  have hf (a : Fin 3) : ContDiff ℝ ∞ (f a) :=
    contDiff_referenceFrameDerivative g1 hg1 L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hZ : nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR =
      coreDefectAction hO hD hF g1 hg1 L lam δ R p hδ hR := by
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    change nativeZField hO hD hF g1 hg1 L lam δ R p G = _
    exact nativeZField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR G
  have hWscalar (a : Fin 3) (G : smoothCompactFiniteSphereCore hO hD) :
      W2 (coreScalar hO hD (f a) (hf a) G) x = f a x • W2 G x := by
    have hc := scalarCentral_coreWeightOperator hO hD (besselWeight 2) (f a) (hf a)
    have he := congrArg
      (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => A G x) hc.eq
    change W2 (coreScalar hO hD (f a) (hf a) G) x = f a x • W2 G x at he
    exact he
  have hWZ : W2 (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F) x =
      (∑ a : Fin 3, f a x • ((normalizedDerivative hF hO hD a).comp T)) (W3 F x) := by
    rw [hZ]
    simp only [coreDefectAction, LinearMap.sum_apply, Module.End.mul_apply, map_sum,
      Submodule.coe_sum, Finset.sum_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro a ha
    change W2 (coreScalar hO hD (f a) (hf a) (coreDerivative hO hD hF a F)) x =
      f a x • ((normalizedDerivative hF hO hD a).comp T) (W3 F x)
    rw [hWscalar a (coreDerivative hO hD hF a F)]
    exact congrArg (fun u : SphereL2 => f a x • u)
      (coreWeight_two_derivative_apply_eq_normalized_third_weight hO hD hF a F x)
  change nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
    (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F) x = _
  rw [nativeC_secondAngularCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
    (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR F) x, hWZ]
  simp only [nativeCZThirdAngularCoefficient, ContinuousLinearMap.comp_apply, f, T, Id, I, W3]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
