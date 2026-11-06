import Calderon.ActualFiniteHarmonicModelPrincipalZScalarAction
import Calderon.ActualFiniteHarmonicModelPrincipalFirstZDerivative
import Calderon.ActualFiniteHarmonicModelPrincipalSecondZDerivative

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualScalarPrincipalAdjoint ActualNormalizedSecondModelErrorAssembly
  NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth ReferenceDensityBounds
  PrincipalCommutator AmbientReferenceRaising ConformalDepth SmoothMetricFrame MovingFrameConnection
  CoordinateBootstrapJets ActualReferenceDDHigherGeometryJets ActualReferenceDDHigherHCoframeJets
  ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev principalZWordScalarFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] principalZWordScalarFunction

lemma coordinateFieldWordPartial_scalar_const_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (T : E) :
    coordinateFieldWordPartial w (fun y => f y • T) =
      fun y => coordinateFieldWordPartial w f y • T := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k)
      (coordinateFieldWordPartial w (fun y => f y • T)) = _
    rw [ih]
    funext x
    have ht := directionalFDeriv_smul (coordinateDirection k)
      (coordinateFieldWordPartial w f) (fun _ : R3 => T)
      (contDiff_coordinateFieldWordPartial w f hf) contDiff_const x
    simpa only [coordinateFieldWordPartial,directionalFDeriv,fderiv_const_apply,
      ContinuousLinearMap.zero_apply,smul_zero,add_zero] using ht

def nativePrincipalDefectWordScalarCoefficient
    (g1 g2 : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (i j a : Fin 3) (w : List (Fin 3)) : R3 → ℝ :=
  fun x => actualPrincipalMatrix g1 L lam δ R p
    (referenceNormalizedPrincipalDifference g1 g2 L lam) x i j *
    coordinateFieldWordPartial w
      (referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y))) x

lemma contDiff_nativePrincipalDefectWordScalarCoefficient
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (i j a : Fin 3) (w : List (Fin 3)) :
    ContDiff ℝ ∞ (nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a w) := by
  exact (ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g1 hg1
    L lam δ R p (referenceNormalizedPrincipalDifference g1 g2 L lam) hδ hR
    (fun b c => contDiff_referenceNormalizedPrincipalDifference_entry
      g1 g2 hg1 hg2 L lam b c) i j).mul
    (contDiff_coordinateFieldWordPartial w _
      (contDiff_referenceFrameDerivative g1 hg1 L lam a _
        (contDiff_log_referenceRadius_profile δ R L p hδ hR)))

lemma nativeReferenceDefectFirstNormalizedCoefficient_word_sum
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (w : List (Fin 3)) (x : R3) :
    coordinateFieldWordPartial w
      (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g L lam δ R p) x =
    ∑ a : Fin 3, coordinateFieldWordPartial w
      (referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))) x •
      BoundedAngularShift.normalizedDerivative hF hO hD a := by
  let f (a : Fin 3) : R3 → ℝ :=
    referenceFrameDerivative g L lam a (fun y => Real.log (referenceRadius δ R p L y))
  have hf (a : Fin 3) : ContDiff ℝ ∞ (f a) :=
    contDiff_referenceFrameDerivative g hg L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR)
  unfold nativeReferenceDefectFirstNormalizedCoefficient
  rw [coordinateFieldWordPartial_sum w
    (fun a y => f a y • BoundedAngularShift.normalizedDerivative hF hO hD a)
    (fun a => (hf a).smul contDiff_const)]
  apply Finset.sum_congr rfl
  intro a ha
  exact congrFun (coordinateFieldWordPartial_scalar_const_smul w (f a) (hf a) _) x

lemma nativePrincipalDefectWordScalarCoefficient_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R)
    (i j : Fin 3) (w : List (Fin 3))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    actualPrincipalMatrix g1 L lam δ R p
      (referenceNormalizedPrincipalDifference g1 g2 L lam) x i j •
      (coordinateFieldWordPartial w
        (nativeReferenceDefectFirstNormalizedCoefficient hO hD hF g1 L lam δ R p) x
          (coreWeightOperator hO hD (besselWeight 1) F x)) =
    ∑ a : Fin 3, nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a w x •
      coreDerivative hO hD hF a F x := by
  rw [nativeReferenceDefectFirstNormalizedCoefficient_word_sum hO hD hF g1 hg1
    L lam δ R p hδ hR w x]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,Finset.smul_sum,
    smul_smul,nativePrincipalDefectWordScalarCoefficient,coreDerivative,Module.End.mul_apply,
    coreNormalizedDerivative,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk]

lemma nativePrincipalCoefficient_first_coefficientDerivative_nativeZ_scalar_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (i j k : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
        (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) F x =
      ∑ a : Fin 3, nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [k] x •
        coreDerivative hO hD hF a F x := by
  rw [nativePrincipalCoefficient_coefficientDerivative_nativeZ_firstAngular_apply]
  exact nativePrincipalDefectWordScalarCoefficient_action hO hD hF g1 g2 hg1
    L lam δ R p hδ hR i j [k] F x

lemma nativePrincipalCoefficient_second_coefficientDerivative_nativeZ_scalar_action
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (i j : Fin 3)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j *
      coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection i))
        (coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection j))
          (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR))) F x =
      ∑ a : Fin 3, nativePrincipalDefectWordScalarCoefficient g1 g2 L lam δ R p i j a [i,j] x •
        coreDerivative hO hD hF a F x := by
  rw [nativePrincipalCoefficient_second_coefficientDerivative_nativeZ_firstAngular_apply]
  exact nativePrincipalDefectWordScalarCoefficient_action hO hD hF g1 g2 hg1
    L lam δ R p hδ hR i j [i,j] F x

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
