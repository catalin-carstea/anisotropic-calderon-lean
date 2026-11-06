import Calderon.ActualFiniteHarmonicModelNativeCoefficients
import Calderon.ActualFiniteHarmonicCoreCoefficientDerivative

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
private abbrev nativeBCFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeBCFunction

lemma nativeB_eq_coreModelFirst (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR =
      coreModelFirstCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR *
        coreWeightOperator hO hD (besselWeight 1) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeBField hO hD hF g1 g2 hg1 L lam δ R p j F = _
  exact nativeBField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR F

lemma nativeC_eq_coreModelZero (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR = coreModelZeroCoefficientAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeCField hO hD hF g1 g2 hg1 L lam δ R p F = _
  exact nativeCField_eq_coreAction hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR F

lemma nativeB_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ScalarCentral hO hD (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR) := by
  intro c hc
  change nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR * coreScalar hO hD c hc =
    coreScalar hO hD c hc * nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hw := congrArg
    (fun T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) => T F x)
    (scalarCentral_coreWeightOperator hO hD (besselWeight 1) c hc).eq
  change coreWeightOperator hO hD (besselWeight 1) (coreScalar hO hD c hc F) x =
    c x • coreWeightOperator hO hD (besselWeight 1) F x at hw
  change nativeBField hO hD hF g1 g2 hg1 L lam δ R p j (coreScalar hO hD c hc F) x =
    c x • nativeBField hO hD hF g1 g2 hg1 L lam δ R p j F x
  unfold nativeBField
  rw [hw, map_smul]


lemma nativeC_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ScalarCentral hO hD (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  rw [nativeC_eq_coreModelZero hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  unfold coreModelZeroCoefficientAction
  dsimp only
  apply scalarCentral_add hO hD
  · apply scalarCentral_add hO hD
    · apply scalarCentral_add hO hD
      · apply scalarCentral_add hO hD
        · apply scalarCentral_mul hO hD
          · exact scalarCentral_coreCoefficientAction hO hD _ _ _
          · exact scalarCentral_coreWeightOperator hO hD _
        · apply scalarCentral_sum hO hD
          intro i hi
          apply scalarCentral_mul hO hD
          · apply scalarCentral_mul hO hD
            · exact scalarCentral_coreScalar hO hD _ _
            · exact scalarCentral_coreNormalizedRaising hO hD _ _
          · apply scalarCentral_sub hO hD
            · exact scalarCentral_coreWeightOperator hO hD _
            · exact scalarCentral_coreWeightOperator hO hD _
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
  · apply scalarCentral_mul hO hD
    · exact scalarCentral_coreCoefficientAction hO hD _ _ _
    · exact scalarCentral_coreWeightOperator hO hD _


lemma nativeB_coefficientDerivative_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) (v : R3) :
    ScalarCentral hO hD (coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativeB hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)) := by
  exact scalarCentral_coefficientDerivative hO hD v _
    (nativeB_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j)

lemma nativeC_coefficientDerivative_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (v : R3) :
    ScalarCentral hO hD (coefficientDerivative (coreDirectionalDerivative hO hD v)
      (nativeC hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)) := by
  exact scalarCentral_coefficientDerivative hO hD v _ (nativeC_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
