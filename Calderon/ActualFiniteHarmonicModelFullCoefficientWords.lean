import Calderon.ActualFiniteHarmonicModelNativeWords
import Calderon.ActualFirstOrderCommutatorWords

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualFiniteHarmonicAmbient
  SpectralWeightedGraph ActualNormalizedSecondModelErrorAssembly
  ActualNormalizedSecondModelCoefficients ActualNormalizedSecondModelDefectCoefficients
  ActualScalarPrincipalAdjoint ReferenceDensityBounds NormalizedPrincipalMetric
  PrincipalCommutator ConformalDepth SmoothSphereFields SmoothAngularApplication
  ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeFullWordsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeFullWordsFunction

def nativeDefectReferenceCommutatorWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  firstFirstSecondBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (fun j => nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR) +
    firstFirstFirstBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (fun j => nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR) (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR) +
    firstFirstZeroBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (fun j => nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR) (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)

def nativeFullErrorCoefficientWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  nativeFirstDefectCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR +
    2 * nativeDefectReferenceCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR -
    2 * ((secondBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) +
    firstBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) +
    zeroBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) + nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR * nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

lemma nativeDefectReference_commutator_words (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    commutator (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR - nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) =
      nativeDefectReferenceCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  rw [nativeUdag_sub_eq_modelFirstOrder hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR, nativeT_eq_modelFirstOrder hO hD hF g1 hg1 L lam δ R p hδ hR]
  unfold nativeDefectReferenceCommutatorWords
  exact first_first_order_commutator_words _ _ _ _ _
    (fun i j => coreDirectionalDerivative_commute hO hD _ _)

lemma nativeErrorCoefficientWords_eq_fullCoefficientWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = nativeFullErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  unfold nativeErrorCoefficientWords nativeFullErrorCoefficientWords
  rw [nativeDefectReference_commutator_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]

lemma nativeFullErrorExpression_eq_fullCoefficientWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = nativeFullErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  exact (nativeFullErrorExpression_eq_coefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR).trans
    (nativeErrorCoefficientWords_eq_fullCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

lemma nativeFullErrorExpression_fullCoefficientWords_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x = nativeFullErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  exact congrArg
    (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => A F x)
    (nativeFullErrorExpression_eq_fullCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
