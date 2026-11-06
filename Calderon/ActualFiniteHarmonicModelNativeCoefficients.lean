import Calderon.ActualFiniteHarmonicCoreScalarCentral
import Calderon.ActualFiniteHarmonicModelError
import Calderon.ActualModelCommutatorWords
import Calderon.ActualMixedDensityScalarZeroFactorSmoothness

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
private abbrev nativeCoefficientFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeCoefficientFunction

def nativePrincipalCoefficient (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (i j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD
    (fun x => referenceRadius δ R p L x * referenceNormalizedPrincipalMatrix g1 g2 L lam x i j)
    (OAI.AnisotropicCalderon.ActualMixedDensityScalarZeroForm.contDiff_referenceRadius_mul_referenceNormalizedPrincipalMatrix_entry
      g1 g2 hg1 hg2 L lam δ R p hδ hR i j)

lemma nativeU_eq_coreModelErrorAction (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = coreModelErrorAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeUField hO hD hF g1 g2 hg1 L lam δ R p F = _
  exact nativeUField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F

lemma nativeUdag_eq_coreModelErrorAdjointAction (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = coreModelErrorAdjointAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeUdagField hO hD hF g1 g2 hg1 L lam δ R p F = _
  exact nativeUdagField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F

lemma nativeV_eq_coreModelDefectFirst (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR =
      coreModelDefectFirstCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
        coreWeightOperator hO hD (besselWeight 1) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeVField hO hD hF g1 g2 hg1 L lam δ R p j F = _
  exact nativeVField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F

lemma nativeW_eq_coreModelDefectZero (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = coreModelDefectZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeWField hO hD hF g1 g2 hg1 L lam δ R p F = _
  exact nativeWField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F

lemma nativeV_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ScalarCentral hO hD (nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) := by
  intro c hc
  change nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR * coreScalar hO hD c hc =
    coreScalar hO hD c hc * nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hw := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
    (scalarCentral_coreWeightOperator hO hD (besselWeight 1) c hc).eq
  change coreWeightOperator hO hD (besselWeight 1) (coreScalar hO hD c hc F) x =
    c x • coreWeightOperator hO hD (besselWeight 1) F x at hw
  change nativeVField hO hD hF g1 g2 hg1 L lam δ R p j (coreScalar hO hD c hc F) x =
    c x • nativeVField hO hD hF g1 g2 hg1 L lam δ R p j F x
  unfold nativeVField
  rw [hw, map_smul]


lemma nativeW_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ScalarCentral hO hD (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  rw [nativeW_eq_coreModelDefectZero hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  unfold coreModelDefectZeroCoefficientAction
  dsimp only
  apply scalarCentral_sub hO hD
  · apply scalarCentral_add hO hD
    · apply scalarCentral_add hO hD
      · apply scalarCentral_add hO hD
        · apply scalarCentral_add hO hD
          · apply scalarCentral_add hO hD
            · apply scalarCentral_add hO hD
              · apply scalarCentral_sub hO hD
                · exact scalarCentral_coreScalar hO hD _ _
                · apply scalarCentral_mul hO hD
                  · exact scalarCentral_coreScalar hO hD _ _
                  · apply scalarCentral_sum hO hD
                    intro i hi
                    apply scalarCentral_mul hO hD
                    · exact scalarCentral_coreCoefficientAction hO hD _ _ _
                    · exact scalarCentral_coreWeightOperator hO hD _
              · apply scalarCentral_mul hO hD
                · apply scalarCentral_sub hO hD
                  · exact scalarCentral_coreCoefficientAction hO hD _ _ _
                  · exact scalarCentral_coreCoefficientAction hO hD _ _ _
                · exact scalarCentral_coreWeightOperator hO hD _
            · apply scalarCentral_sum hO hD
              intro i hi
              apply scalarCentral_mul hO hD
              · exact scalarCentral_coreScalar hO hD _ _
              · exact scalarCentral_coreDerivative hO hD _ _
          · apply scalarCentral_sub hO hD
            · apply scalarCentral_sum hO hD
              intro i hi
              apply scalarCentral_mul hO hD
              · apply scalarCentral_mul hO hD
                · exact scalarCentral_coreScalar hO hD _ _
                · exact scalarCentral_coreNormalizedDerivative hO hD _ _
              · apply scalarCentral_sub hO hD
                · exact scalarCentral_coreWeightOperator hO hD _
                · apply scalarCentral_smul hO hD
                  exact scalarCentral_coreWeightOperator hO hD _
            · apply scalarCentral_sum hO hD
              intro i hi
              apply scalarCentral_mul hO hD
              · apply scalarCentral_mul hO hD
                · exact scalarCentral_coreScalar hO hD _ _
                · exact scalarCentral_coreNormalizedRaising hO hD _ _
              · apply scalarCentral_sub hO hD
                · exact scalarCentral_coreWeightOperator hO hD _
                · exact scalarCentral_coreWeightOperator hO hD _
        · apply scalarCentral_sub hO hD
          · apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_mul hO hD
            · apply scalarCentral_mul hO hD
              · exact scalarCentral_coreScalar hO hD _ _
              · exact scalarCentral_coreRotation hO hD _ _
            · exact scalarCentral_coreDerivative hO hD _ _
          · apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_mul hO hD
            · apply scalarCentral_mul hO hD
              · exact scalarCentral_coreScalar hO hD _ _
              · exact scalarCentral_coreRaising hO hD _ _
            · exact scalarCentral_coreRotation hO hD _ _
      · apply scalarCentral_sub hO hD
        · apply scalarCentral_sum hO hD
          intro i hi
          apply scalarCentral_sum hO hD
          intro i hi
          apply scalarCentral_mul hO hD
          · apply scalarCentral_mul hO hD
            · apply scalarCentral_mul hO hD
              · exact scalarCentral_coreScalar hO hD _ _
              · exact scalarCentral_coreNormalizedDerivative hO hD _ _
            · exact scalarCentral_coreWeightOperator hO hD _
          · exact scalarCentral_coreDerivative hO hD _ _
        · apply scalarCentral_sum hO hD
          intro i hi
          apply scalarCentral_sum hO hD
          intro i hi
          apply scalarCentral_mul hO hD
          · apply scalarCentral_mul hO hD
            · apply scalarCentral_mul hO hD
              · exact scalarCentral_coreScalar hO hD _ _
              · exact scalarCentral_coreNormalizedRaising hO hD _ _
            · exact scalarCentral_coreWeightOperator hO hD _
          · exact scalarCentral_coreRaising hO hD _ _
    · apply scalarCentral_smul hO hD
      apply scalarCentral_mul hO hD
      · exact scalarCentral_coreScalar hO hD _ _
      · apply scalarCentral_sum hO hD
        intro i hi
        apply scalarCentral_mul hO hD
        · exact scalarCentral_coreScalar hO hD _ _
        · apply scalarCentral_smul hO hD
          apply scalarCentral_sum hO hD
          intro i hi
          apply scalarCentral_sum hO hD
          intro i hi
          apply scalarCentral_mul hO hD
          · exact scalarCentral_coreScalar hO hD _ _
          · exact scalarCentral_coreRotation hO hD _ _
  · exact scalarCentral_coreScalar hO hD _ _


lemma nativeU_eq_modelSecondOrder (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = modelSecondOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  rw [nativeU_eq_coreModelErrorAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  rfl

lemma nativeUdag_sub_eq_modelFirstOrder (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR - nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR =
      modelFirstOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i))
        (fun j => nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)
        (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  rw [nativeUdag_eq_coreModelErrorAdjointAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR, nativeU_eq_coreModelErrorAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  unfold coreModelErrorAdjointAction modelFirstOrder
  abel

lemma nativeU_right_product_words (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR * (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) =
      secondBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) +
      firstBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) +
      zeroBaseRightProduct (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR) (fun j => nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeZ hO hD hF g1 hg1 L lam δ R p hδ hR) := by
  rw [nativeU_eq_modelSecondOrder hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  exact second_order_right_product_words _ _ _ _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
