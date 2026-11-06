import Calderon.ActualFiniteHarmonicModelFirstDefect
import Calderon.ActualFiniteHarmonicCoreFirstSecondWords
import Calderon.ActualFiniteHarmonicModelFirstSecondWords
import Calderon.ActualFiniteHarmonicModelCommutatorTransport

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
private abbrev nativeWordsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeWordsFunction

def nativeFirstDefectCommutatorWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  secondBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) +
    firstBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) +
    zeroBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

def nativeErrorCoefficientWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  nativeFirstDefectCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR +
    2 * commutator (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR - nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) -
    2 * ((secondBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) +
    firstBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) +
    zeroBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR)) + nativeZdag hO hD hF g1 hg1 L lam δ R p hδ hR * nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

lemma nativeFirstDefectCommutatorWords_eq_explicit (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeFirstDefectCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR =
  secondBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) +
    firstBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) +
    zeroBaseWords (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  delta nativeFirstDefectCommutatorWords
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply]

lemma nativeFirstDefect_commutator_words (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    commutator (2 * (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR - nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) +
      (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR - nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) (nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) =
      nativeFirstDefectCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  have ht := nativeFirstDefect_commutator_eq_model hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hw := native_model_first_second_order_commutator_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  have hf := nativeFirstDefectCommutatorWords_eq_explicit hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  exact ht.trans (hw.trans hf.symm)


lemma nativeFirstDefect_commutator_words_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    commutator (2 * (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR - nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) +
      (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR - nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) (nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) F x =
      nativeFirstDefectCommutatorWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  exact congrArg
    (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => A F x)
    (nativeFirstDefect_commutator_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

lemma nativeReducedErrorExpression_eq_coefficientWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeReducedErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = nativeErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  unfold nativeReducedErrorExpression nativeErrorCoefficientWords
  dsimp only
  rw [nativeFirstDefect_commutator_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR, nativeU_right_product_words hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]

lemma nativeFullErrorExpression_eq_coefficientWords (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = nativeErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  exact (nativeFullErrorExpression_eq_reduced hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR).trans
    (nativeReducedErrorExpression_eq_coefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

lemma nativeFullErrorExpression_coefficientWords_apply (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    nativeFullErrorExpression hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x = nativeErrorCoefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F x := by
  exact congrArg
    (fun A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => A F x)
    (nativeFullErrorExpression_eq_coefficientWords hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
