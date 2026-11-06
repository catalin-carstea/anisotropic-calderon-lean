import Calderon.ActualFiniteHarmonicModelNativeCoefficients
import Calderon.ActualFiniteHarmonicModelErrorWords
import Calderon.ActualModelFirstOrderCoefficientAlgebra

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
  ActualModelCommutatorWords SmoothMetricFrame MovingFrameConnection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeDefectFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeDefectFunction

def nativeReferenceFrameScalar (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (a j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD
    (fun y => referenceMetricGramFrame g1 L (lam,y) a j)
    ((contDiff_piLp_apply (p := 2) (i := j) :
      ContDiff ℝ ∞ (fun v : R3 => v j)).comp
        (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a))

def nativeReferenceConnectionAction (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (a : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  (1/2 : ℝ) • ∑ b : Fin 3, ∑ c : Fin 3,
    coreScalar hO hD
      (fun y => referenceFrameConnectionCoefficient g1 L lam y
        (referenceMetricGramFrame g1 L (lam,y) a) b c)
      (AmbientReferenceCovariantCore.contDiff_referenceFrameConnectionCoefficient_field
        g1 hg1 L lam _ (contDiff_referenceMetricGramFrame_slice g1 hg1 L lam a) b c) *
      coreRotation hO hD b c

def nativeReferenceProfileScalar (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (a : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  coreScalar hO hD
    (AmbientReferenceRaising.referenceFrameDerivative g1 L lam a (fun y => Real.log (referenceRadius δ R p L y)))
    (AmbientReferenceRaising.contDiff_referenceFrameDerivative g1 hg1 L lam a _
      (contDiff_log_referenceRadius_profile δ R L p hδ hR))

def nativeReferenceFirstCoefficient (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, coreRaising hO hD hF a * nativeReferenceFrameScalar hO hD g1 hg1 L lam a j

def nativeReferenceZeroCoefficient (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, coreRaising hO hD hF a *
    (nativeReferenceConnectionAction hO hD g1 hg1 L lam a + nativeReferenceProfileScalar hO hD g1 hg1 L lam δ R p hδ hR a * coreDegree hO hD)

def nativeReferenceAdjointFirstCoefficient (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, ((-1 : ℝ) • (coreNormalizedDerivative hO hD hF a * coreWeightOperator hO hD (besselWeight 1))) * nativeReferenceFrameScalar hO hD g1 hg1 L lam a j

def nativeReferenceAdjointZeroCoefficient (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  ∑ a : Fin 3, coreNormalizedDerivative hO hD hF a *
    ((-1 : ℝ) • (coreWeightOperator hO hD (besselWeight 1) * nativeReferenceConnectionAction hO hD g1 hg1 L lam a) +
      nativeReferenceProfileScalar hO hD g1 hg1 L lam δ R p hδ hR a * (coreWeightOperator hO hD (besselWeight 2) - (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1)))

def nativeH (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  2 * (nativeReferenceAdjointFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j -
    nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR j) +
      nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR

def nativeH0 (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) :=
  2 * (nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR -
    nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR) + nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR

lemma coreReferenceHorizontal_eq_coefficients (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1) (L lam : ℝ) (a : Fin 3) :
    coreReferenceHorizontal hO hD g1 hg1 L lam a =
      (∑ j : Fin 3, nativeReferenceFrameScalar hO hD g1 hg1 L lam a j * coreDirectionalDerivative hO hD (coordinateDirection j)) +
      nativeReferenceConnectionAction hO hD g1 hg1 L lam a := by
  rfl

lemma nativeT_eq_coreReferenceRaisingAction (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    nativeT hO hD hF g1 hg1 L lam δ R p hδ hR = coreReferenceRaisingAction hO hD hF g1 hg1 L lam δ R p hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeTField hO hD hF g1 hg1 L lam δ R p F = _
  exact nativeTField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR F

lemma nativeTdag_eq_coreReferenceAdjointAction (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR = coreReferenceAdjointAction hO hD hF g1 hg1 L lam δ R p hδ hR := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  change nativeTdagField hO hD hF g1 hg1 L lam δ R p F = _
  exact nativeTdagField_eq_coreAction hO hD hF g1 hg1 L lam δ R p hδ hR F

lemma nativeT_eq_modelFirstOrder (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    nativeT hO hD hF g1 hg1 L lam δ R p hδ hR =
      modelFirstOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
        (nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR) := by
  rw [nativeT_eq_coreReferenceRaisingAction hO hD hF g1 hg1 L lam δ R p hδ hR]
  unfold coreReferenceRaisingAction coreReferenceInput
  simp_rw [coreReferenceHorizontal_eq_coefficients hO hD g1 hg1 L lam]
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  simp only [modelFirstOrder, nativeReferenceFirstCoefficient,
    nativeReferenceZeroCoefficient, nativeReferenceProfileScalar, Fin.sum_univ_three,
    LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    map_add, map_smul, RingHom.id_apply, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply]
  abel


lemma nativeTdag_eq_modelFirstOrder (hF : SphereFischerInner) (g1 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ) (hδ : 0 < δ) (hR : 0 < R) :
    nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR =
      modelFirstOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeReferenceAdjointFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
        (nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR) := by
  rw [nativeTdag_eq_coreReferenceAdjointAction hO hD hF g1 hg1 L lam δ R p hδ hR]
  unfold coreReferenceAdjointAction
  simp_rw [coreReferenceHorizontal_eq_coefficients hO hD g1 hg1 L lam]
  unfold nativeReferenceAdjointFirstCoefficient nativeReferenceAdjointZeroCoefficient
  simpa only [nativeReferenceProfileScalar] using
    modelFirstOrder_referenceAdjoint_decomposition
      (fun i => coreDirectionalDerivative hO hD (coordinateDirection i))
      (coreNormalizedDerivative hO hD hF)
      (coreWeightOperator hO hD (besselWeight 1))
      (coreWeightOperator hO hD (besselWeight 2) -
        (2 : ℝ) • coreWeightOperator hO hD (besselWeight 1))
      (nativeReferenceFrameScalar hO hD g1 hg1 L lam)
      (nativeReferenceConnectionAction hO hD g1 hg1 L lam)
      (nativeReferenceProfileScalar hO hD g1 hg1 L lam δ R p hδ hR)


lemma nativeFirstDefect_eq_modelFirstOrder (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    2 * (nativeTdag hO hD hF g1 hg1 L lam δ R p hδ hR - nativeT hO hD hF g1 hg1 L lam δ R p hδ hR) +
      (nativeUdag hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR - nativeU hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) =
      modelFirstOrder (fun i => coreDirectionalDerivative hO hD (coordinateDirection i)) (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  rw [nativeTdag_eq_modelFirstOrder hO hD hF g1 hg1 L lam δ R p hδ hR, nativeT_eq_modelFirstOrder hO hD hF g1 hg1 L lam δ R p hδ hR,
    nativeUdag_sub_eq_modelFirstOrder hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR]
  unfold nativeH nativeH0
  exact modelFirstOrder_firstDefect
    (fun i => coreDirectionalDerivative hO hD (coordinateDirection i))
    (nativeReferenceFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeReferenceAdjointFirstCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
    (fun j => nativeV hO hD hF g1 g2 hg1 L lam δ R p j hg2 hδ hR)
    (nativeReferenceZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeReferenceAdjointZeroCoefficient hO hD hF g1 hg1 L lam δ R p hδ hR)
    (nativeW hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)


lemma nativeH_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (j : Fin 3) :
    ScalarCentral hO hD (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j) := by
  have htwo : ScalarCentral hO hD
      (2 : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) := by
    intro c hc
    exact (2 : ℕ).cast_commute _
  unfold nativeH nativeReferenceAdjointFirstCoefficient nativeReferenceFirstCoefficient
    nativeReferenceFrameScalar
  apply scalarCentral_add hO hD
  · apply scalarCentral_mul hO hD
    · exact htwo
    · apply scalarCentral_sub hO hD
      · apply scalarCentral_sum hO hD
        intro i hi
        apply scalarCentral_mul hO hD
        · apply scalarCentral_smul hO hD
          apply scalarCentral_mul hO hD
          · exact scalarCentral_coreNormalizedDerivative hO hD _ _
          · exact scalarCentral_coreWeightOperator hO hD _
        · exact scalarCentral_coreScalar hO hD _ _
      · apply scalarCentral_sum hO hD
        intro i hi
        apply scalarCentral_mul hO hD
        · exact scalarCentral_coreRaising hO hD _ _
        · exact scalarCentral_coreScalar hO hD _ _
  · exact nativeV_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR j


lemma nativeH0_scalarCentral (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) :
    ScalarCentral hO hD (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR) := by
  have htwo : ScalarCentral hO hD
      (2 : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) := by
    intro c hc
    exact (2 : ℕ).cast_commute _
  unfold nativeH0 nativeReferenceAdjointZeroCoefficient nativeReferenceZeroCoefficient
    nativeReferenceConnectionAction nativeReferenceProfileScalar coreDegree
  apply scalarCentral_add hO hD
  · apply scalarCentral_mul hO hD
    · exact htwo
    · apply scalarCentral_sub hO hD
      · apply scalarCentral_sum hO hD
        intro i hi
        apply scalarCentral_mul hO hD
        · exact scalarCentral_coreNormalizedDerivative hO hD _ _
        · apply scalarCentral_add hO hD
          · apply scalarCentral_smul hO hD
            apply scalarCentral_mul hO hD
            · exact scalarCentral_coreWeightOperator hO hD _
            · apply scalarCentral_smul hO hD
              apply scalarCentral_sum hO hD
              intro i hi
              apply scalarCentral_sum hO hD
              intro i hi
              apply scalarCentral_mul hO hD
              · exact scalarCentral_coreScalar hO hD _ _
              · exact scalarCentral_coreRotation hO hD _ _
          · apply scalarCentral_mul hO hD
            · exact scalarCentral_coreScalar hO hD _ _
            · apply scalarCentral_sub hO hD
              · exact scalarCentral_coreWeightOperator hO hD _
              · apply scalarCentral_smul hO hD
                exact scalarCentral_coreWeightOperator hO hD _
      · apply scalarCentral_sum hO hD
        intro i hi
        apply scalarCentral_mul hO hD
        · exact scalarCentral_coreRaising hO hD _ _
        · apply scalarCentral_add hO hD
          · apply scalarCentral_smul hO hD
            apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_sum hO hD
            intro i hi
            apply scalarCentral_mul hO hD
            · exact scalarCentral_coreScalar hO hD _ _
            · exact scalarCentral_coreRotation hO hD _ _
          · apply scalarCentral_mul hO hD
            · exact scalarCentral_coreScalar hO hD _ _
            · exact scalarCentral_coreWeightOperator hO hD _
  · exact nativeW_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR


lemma nativeH_commute_principal (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (l i j : Fin 3) :
    Commute (nativeH hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l)
      (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j) := by
  exact nativeH_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR l _ _

lemma nativeH0_commute_principal (hF : SphereFischerInner) (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (L lam δ R : ℝ) (p : ℕ)
    (hg2 : IsAdmissibleMetric g2) (hδ : 0 < δ) (hR : 0 < R) (i j : Fin 3) :
    Commute (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
      (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i j) := by
  exact nativeH0_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
