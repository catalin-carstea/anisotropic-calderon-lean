import Calderon.ActualFiniteHarmonicModelReferenceDefectFirstNormalized
import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualModelCommutatorWords ActualReferenceDDHigherLogFrameJets
  AmbientReferenceRaising PrincipalCommutator ConformalDepth SmoothMetricFrame MovingFrameConnection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeZCoefficientDerivativeFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeZCoefficientDerivativeFunction

lemma contDiff_nativeReferenceDefectFirstNormalizedCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p) := by
  let f (a : Fin 3) : R3 → ℝ :=
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hf (a : Fin 3) : ContDiff ℝ ∞ (f a) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold nativeReferenceDefectFirstNormalizedCoefficient
  exact ContDiff.sum (fun a _ => (hf a).smul contDiff_const)

lemma nativeZ_firstNormalizedCoefficient_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeZ hO hD hF g hg L lam δ R p hδ hR F x =
      nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  change nativeZField hO hD hF g hg L lam δ R p F x = _
  exact nativeZField_eq_referenceDefectFirstNormalizedCoefficient
    hO hD hF g hg L lam δ R p hδ hR F x

lemma coefficientDerivative_nativeZ_firstNormalized_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (v : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativeZ hO hD hF g hg L lam δ R p hδ hR) F x =
      directionalFDeriv v (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p) x
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  have hact : (fun y => nativeZ hO hD hF g hg L lam δ R p hδ hR F y) =
      (fun y => (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p) y (U y)) :=
    funext (fun y => nativeZ_firstNormalizedCoefficient_apply hO hD hF g hg L lam δ R p hδ hR F y)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => nativeZ hO hD hF g hg L lam δ R p hδ hR F y) x -
      nativeZ hO hD hF g hg L lam δ R p hδ hR (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,nativeZ_firstNormalizedCoefficient_apply hO hD hF g hg L lam δ R p hδ hR
    (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v
    (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p)
    (U : R3 → SphereL2)
    (contDiff_nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g hg L lam δ R p hδ hR)
    U.property.1 x,hW]
  abel

lemma coefficientDerivative_second_nativeZ_firstNormalized_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (v u : R3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coefficientDerivative (coreDirectionalDerivative hO hD v)
      (coefficientDerivative (coreDirectionalDerivative hO hD u)
        (nativeZ hO hD hF g hg L lam δ R p hδ hR)) F x =
      directionalFDeriv v (directionalFDeriv u
        (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p)) x
          (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let U : smoothCompactFiniteSphereCore hO hD := coreWeightOperator hO hD (besselWeight 1) F
  let A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
    coefficientDerivative (coreDirectionalDerivative hO hD u)
      (nativeZ hO hD hF g hg L lam δ R p hδ hR)
  have ha (G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
      A G y = directionalFDeriv u
        (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p) y
          (coreWeightOperator hO hD (besselWeight 1) G y) :=
    coefficientDerivative_nativeZ_firstNormalized_apply hO hD hF g hg L lam δ R p hδ hR u G y
  have hact : (fun y => A F y) =
      (fun y => directionalFDeriv u
        (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p) y (U y)) :=
    funext (ha F)
  have hW : coreWeightOperator hO hD (besselWeight 1) (coreDirectionalDerivative hO hD v F) x =
      directionalFDeriv v (U : R3 → SphereL2) x :=
    congrArg (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
      (coreWeightOperator_directionalDerivative_commute hO hD (besselWeight 1) v).eq
  change directionalFDeriv v (fun y => A F y) x -
      A (coreDirectionalDerivative hO hD v F) x = _
  rw [hact,ha (coreDirectionalDerivative hO hD v F) x]
  rw [directionalFDeriv_clm_apply v
    (directionalFDeriv u (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p))
    (U : R3 → SphereL2)
    (contDiff_directionalFDeriv u _
      (contDiff_nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g hg L lam δ R p hδ hR))
    U.property.1 x,hW]
  abel

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
