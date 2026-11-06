import Calderon.ActualFiniteHarmonicModelReferenceWeights
import Calderon.ActualFiniteHarmonicModelFirstAngularNormalization

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition ActualFiniteHarmonicCore SpectralWeightedGraph
  BoundedAngularShift ActualReferenceParallelRaising ActualReferenceDDSpectralTransport
  ActualReferenceModelTrace AmbientReferenceRaising SmoothMetricFrame MovingFrameConnection
  ReferenceDensityBounds NormalizedPrincipalMetric PrincipalCommutator ConformalDepth
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceZeroAngularFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] referenceZeroAngularFunction

lemma inverseDegreeMultiplier_coreWeight_two_apply
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    inverseDegreeMultiplier hO hD (coreWeightOperator hO hD (besselWeight 2) F x) =
      coreWeightOperator hO hD (besselWeight 1) F x := by
  rw [← coreWeight_one_twice_apply hO hD F x]
  exact inverseDegreeMultiplier_coreWeight_one_apply hO hD
    (coreWeightOperator hO hD (besselWeight 1) F) x

lemma coreWeight_nativeReferenceProfileScalar_apply
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1) (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a F) x =
      referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x •
        (coreWeightOperator hO hD (besselWeight 1) F x) := by
  let f : R3 → ℝ := referenceFrameDerivative g L lam a
    (fun y => Real.log (referenceRadius δ R p L y))
  have hf : ContDiff ℝ ∞ f := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  have hw := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
    (scalarCentral_coreWeightOperator hO hD (besselWeight 1) f hf).eq
  exact hw

def nativeReferenceZeroDefectAngularCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) : R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => (2 : ℝ) • ∑ a : Fin 3,
    (((normalizedDerivative hF hO hD a).comp
      (-(normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)) +
        (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) •
          (ContinuousLinearMap.id ℝ SphereL2 - (2 : ℝ) • inverseDegreeMultiplier hO hD))) -
      ((normalizedRaising hF hO hD a).comp
        ((normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)) +
          (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) •
            (ContinuousLinearMap.id ℝ SphereL2 - inverseDegreeMultiplier hO hD))))

lemma contDiff_nativeReferenceZeroDefectAngularCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    ContDiff ℝ ∞ (nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p) := by
  have hA (a : Fin 3) := contDiff_normalizedReferenceAngularConnection_frame hO hD g hg L lam a
  have hf (a : Fin 3) := contDiff_referenceFrameDerivative g hg L lam a _
    (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold nativeReferenceZeroDefectAngularCoefficient
  apply (contDiff_const : ContDiff ℝ ∞ (fun _ : R3 => (2 : ℝ))).smul
  apply ContDiff.sum
  intro a _
  exact (contDiff_const.clm_comp ((hA a).neg.add ((hf a).smul contDiff_const))).sub
    (contDiff_const.clm_comp ((hA a).add ((hf a).smul contDiff_const)))

lemma nativeReferenceZeroCoefficient_apply_eq_secondAngularField
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR F x =
      ∑ a : Fin 3, normalizedRaising hF hO hD a
        ((normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)) (coreWeightOperator hO hD (besselWeight 2) F x) +
          (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) • (coreWeightOperator hO hD (besselWeight 2) F x - coreWeightOperator hO hD (besselWeight 1) F x)) := by
  simp only [nativeReferenceZeroCoefficient,LinearMap.sum_apply,Module.End.mul_apply,
    Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  change normalizedRaising hF hO hD a
    (coreWeightOperator hO hD (besselWeight 1)
      (nativeReferenceConnectionAction hO hD g hg L lam a F +
        nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a (coreDegree hO hD F)) x) = _
  simp only [map_add,Submodule.coe_add,Pi.add_apply]
  rw [coreWeight_nativeReferenceConnectionAction_apply hO hD g hg L lam a F x,
    coreWeight_nativeReferenceProfileScalar_apply hO hD g hg L lam δ R p hδ hR a
      (coreDegree hO hD F) x,coreWeight_one_degree_apply hO hD F x]

lemma nativeReferenceAdjointZeroCoefficient_apply_eq_secondAngularField
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR F x =
      ∑ a : Fin 3, normalizedDerivative hF hO hD a
        (-((normalizedReferenceAngularConnection hO hD g L lam x (referenceMetricGramFrame g L (lam,x) a)) (coreWeightOperator hO hD (besselWeight 2) F x)) +
          (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y)) x) • (coreWeightOperator hO hD (besselWeight 2) F x - (2 : ℝ) • (coreWeightOperator hO hD (besselWeight 1) F x))) := by
  simp only [nativeReferenceAdjointZeroCoefficient,LinearMap.sum_apply,Module.End.mul_apply,
    Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [coreNormalizedDerivative,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,Module.End.mul_apply,nativeReferenceProfileScalar,coreScalar,
    LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,Submodule.coe_add,Submodule.coe_sub,
    Submodule.coe_smul,Submodule.coe_neg,Pi.neg_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,neg_one_smul]
  rw [coreWeight_nativeReferenceConnectionAction_apply hO hD g hg L lam a F x]

lemma nativeReferenceZeroDefect_secondAngularCoefficient_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g hg L lam δ R p hδ hR -
      nativeReferenceZeroCoefficient hO hD hF g hg L lam δ R p hδ hR)) F x =
      nativeReferenceZeroDefectAngularCoefficient hO hD hF g hg L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  simp only [Module.End.mul_apply,Module.End.ofNat_apply,two_nsmul,
    LinearMap.sub_apply,Submodule.coe_add,Submodule.coe_sub,Pi.add_apply,Pi.sub_apply]
  rw [nativeReferenceAdjointZeroCoefficient_apply_eq_secondAngularField hO hD hF g hg L lam δ R p hδ hR F x,
    nativeReferenceZeroCoefficient_apply_eq_secondAngularField hO hD hF g hg L lam δ R p hδ hR F x]
  unfold nativeReferenceZeroDefectAngularCoefficient
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.id_apply,
    inverseDegreeMultiplier_coreWeight_two_apply hO hD F x]
  rw [Finset.sum_sub_distrib]
  module

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
