import Calderon.ActualFiniteHarmonicModelFirstCoefficientJets
import Calderon.ActualFiniteHarmonicModelReferenceZeroAngular
import Calderon.ActualFiniteHarmonicModelShiftWeights
import Calderon.ActualFiniteHarmonicModelReferenceDefectFirstNormalized

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BoundedAngularShift
  ActualReferenceParallelRaising AmbientReferenceRaising SmoothMetricFrame
  MovingFrameConnection PrincipalCommutator ConformalDepth ReferenceDensityBounds
  ActualNormalizedSecondModelCoefficients
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeBZSecondAngularFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeBZSecondAngularFunction

def nativeReferenceDefectSecondAngularCoefficient
    (hF : SphereFischerInner) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) :
    R3 → SphereL2 →L[ℝ] SphereL2 :=
  fun x => ∑ a : Fin 3,
    referenceFrameDerivative g L lam a
      (fun y => Real.log (referenceRadius δ R p L y)) x •
      (normalizedDerivative hF hO hD a).comp
        (ContinuousLinearMap.id ℝ SphereL2-inverseDegreeMultiplier hO hD)

lemma coreWeight_one_nativeZ_apply
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    coreWeightOperator hO hD (besselWeight 1)
      (nativeZ hO hD hF g hg L lam δ R p hδ hR F) x =
      nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p x
        (coreWeightOperator hO hD (besselWeight 2) F x) := by
  let W := coreWeightOperator hO hD (besselWeight 1)
  let V := coreWeightOperator hO hD (besselWeight 2) F x
  let U := W F x
  let I := inverseDegreeMultiplier hO hD
  have hI : I V = U := by
    simpa only [I,V,U,W] using inverseDegreeMultiplier_coreWeight_two_apply hO hD F x
  have hZ : nativeZ hO hD hF g hg L lam δ R p hδ hR =
      coreDefectAction hO hD hF g hg L lam δ R p hδ hR := by
    apply LinearMap.ext
    intro G
    apply Subtype.ext
    exact nativeZField_eq_coreAction hO hD hF g hg L lam δ R p hδ hR G
  have hterm (a : Fin 3) :
      W (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a
        (coreDerivative hO hD hF a F)) x =
      referenceFrameDerivative g L lam a
        (fun y => Real.log (referenceRadius δ R p L y)) x •
        (normalizedDerivative hF hO hD a).comp
          (ContinuousLinearMap.id ℝ SphereL2-I) V := by
    rw [show W (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a
          (coreDerivative hO hD hF a F)) x =
        referenceFrameDerivative g L lam a
          (fun y => Real.log (referenceRadius δ R p L y)) x •
        W (coreDerivative hO hD hF a F) x from by
          simpa only [W] using coreWeight_nativeReferenceProfileScalar_apply hO hD g hg
            L lam δ R p hδ hR a (coreDerivative hO hD hF a F) x]
    rw [show W (coreDerivative hO hD hF a F) x =
      normalizedDerivative hF hO hD a (V-U) from by
        simpa only [W,V,U] using
          coreWeight_one_derivative_apply_eq_normalized_shift hO hD hF a F x]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply,hI]
  calc
    W (nativeZ hO hD hF g hg L lam δ R p hδ hR F) x =
        W (coreDefectAction hO hD hF g hg L lam δ R p hδ hR F) x := by rw [hZ]
    _ = ∑ a : Fin 3,
        W (nativeReferenceProfileScalar hO hD g hg L lam δ R p hδ hR a
          (coreDerivative hO hD hF a F)) x := by
      simp only [coreDefectAction,nativeReferenceProfileScalar,
        LinearMap.sum_apply,Module.End.mul_apply,map_sum,Submodule.coe_sum,
        Finset.sum_apply]
    _ = ∑ a : Fin 3,
        referenceFrameDerivative g L lam a
          (fun y => Real.log (referenceRadius δ R p L y)) x •
          (normalizedDerivative hF hO hD a).comp
            (ContinuousLinearMap.id ℝ SphereL2-I) V :=
      Finset.sum_congr rfl (fun a _ => hterm a)
    _ = nativeReferenceDefectSecondAngularCoefficient hO hD hF g L lam δ R p x V := by
      simp only [nativeReferenceDefectSecondAngularCoefficient,
        ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,I]

lemma nativeB_nativeZ_secondAngularCoefficient_apply
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (L lam δ R : ℝ) (p : ℕ)
    (j : Fin 3) (hg2 : IsAdmissibleMetric g2)
    (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
      nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) F x =
      (modelFirstNormalizedCoefficient hF hO hD g1 g2 hg1 L lam δ R p j x).comp
        (nativeReferenceDefectSecondAngularCoefficient hO hD hF g1 L lam δ R p x)
          (coreWeightOperator hO hD (besselWeight 2) F x) := by
  rw [Module.End.mul_apply,
    nativeB_firstNormalizedCoefficient_apply hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR,
    coreWeight_one_nativeZ_apply hO hD hF g1 hg1 L lam δ R p hδ hR F x]
  rfl

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
