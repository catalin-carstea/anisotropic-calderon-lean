import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison
import Calderon.ActualFiniteHarmonicModelSupportedScalarEnergyIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph SmoothMetricFrame
  SectionFiveErrorForms ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev horizontalIntegralFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] horizontalIntegralFunction

lemma coreWeightOperator_eq_zero_of_eval_eq_zero (w : ℕ → ℝ)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (hF : F x=0) :
    coreWeightOperator hO hD w F x=0 := by
  change finiteHarmonicBlockCutoff hO hD F.property.2.2.choose
    (fun k => w k • ContinuousLinearMap.id ℝ (harmonicSphereSubspace k)) (F x)=0
  rw [hF,map_zero]

lemma finiteCoreSourceEnergy_eq_zero_of_notMem
    (K : Set R3) (F : smoothCompactFiniteSphereCore hO hD)
    (hsupp : tsupport (F : R3 → SphereL2) ⊆ K) (x : R3) (hx : x ∉ K) (beta : ℝ) :
    finiteCoreSourceEnergy hO hD beta F x=0 := by
  have hF : F x=0 := image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp hy))
  have hd (j : Fin 3) : coreDirectionalDerivative hO hD (coordinateDirection j) F x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hy => hx (hsupp
      (tsupport_coreDirectionalDerivative_subset hO hD (coordinateDirection j) F hy)))
  have hw (w : ℕ → ℝ) := coreWeightOperator_eq_zero_of_eval_eq_zero hO hD w F x hF
  have hwd (j : Fin 3) := coreWeightOperator_eq_zero_of_eval_eq_zero hO hD (besselWeight (1/2:ℝ))
    (coreDirectionalDerivative hO hD (coordinateDirection j) F) x (hd j)
  simp only [finiteCoreSourceEnergy,sourceNormSquareIntegrand,hd,hw,hwd,norm_zero,pow_two,zero_mul,
    Finset.sum_const_zero,mul_zero,add_zero]

theorem integrable_finiteCoreReferenceProfileEnergy
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (beta : R3 → ℝ) (hbeta : Continuous beta) (hpos : ∀ x, 0 < beta x)
    (F : smoothCompactFiniteSphereCore hO hD) :
    Integrable (fun x => referenceDensityFamily g L (lam,x)*
      finiteCoreReferenceProfileEnergy hO hD g hg L lam (beta x) F x) := by
  have hrho := WeightedBaseSpectral.continuous_referenceBaseDensity g hg L lam
  have hinv : Continuous (fun x => (beta x)⁻¹) := hbeta.inv₀ (fun x => (hpos x).ne')
  have hZero : Integrable (fun x => ∑ a : Fin 3,
      referenceDensityFamily g L (lam,x)*‖coreReferenceHorizontal hO hD g hg L lam a F x‖^2) :=
    integrable_finsetSum _ (fun a _ => integrable_native_core_weighted_norm_sq hO hD _ hrho _)
  have hOne : Integrable (fun x => (referenceDensityFamily g L (lam,x)*(beta x)^2)*
      ‖coreWeightOperator hO hD (besselWeight 1) F x‖^2) :=
    integrable_native_core_weighted_norm_sq hO hD _ (hrho.mul (hbeta.pow 2)) _
  have hHalf : Integrable (fun x => ∑ a : Fin 3,
      (referenceDensityFamily g L (lam,x)*(beta x)⁻¹)*
        ‖coreWeightOperator hO hD (besselWeight (1/2:ℝ)) (coreReferenceHorizontal hO hD g hg L lam a F) x‖^2) :=
    integrable_finsetSum _ (fun a _ => integrable_native_core_weighted_norm_sq hO hD _ (hrho.mul hinv) _)
  have hThree : Integrable (fun x => (referenceDensityFamily g L (lam,x)*beta x)*
      ‖coreWeightOperator hO hD (besselWeight (3/2:ℝ)) F x‖^2) :=
    integrable_native_core_weighted_norm_sq hO hD _ (hrho.mul hbeta) _
  apply (((hZero.add hOne).add hHalf).add hThree).congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.add_apply,finiteCoreReferenceProfileEnergy,sourceNormSquareIntegrand,mul_add,
    Finset.mul_sum,mul_assoc]

theorem exists_finiteCoreSourceEnergy_uniform_reference_profile_integral_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ beta : R3 → ℝ, Continuous beta → (∀ x, 0 < beta x) → (∀ x ∈ K, 1 ≤ beta x) →
      ∀ F : smoothCompactFiniteSphereCore hO hD, tsupport (F : R3 → SphereL2) ⊆ K →
      (∫ x : R3, referenceDensityFamily g L (lam,x)*finiteCoreSourceEnergy hO hD (beta x) F x) ≤
        C*∫ x : R3, referenceDensityFamily g L (lam,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L lam (beta x) F x := by
  obtain ⟨C,hC,hpoint⟩ := exists_finiteCoreSourceEnergy_uniform_reference_profile_bound hO hD g hg L K hK
  refine ⟨C,hC,?_⟩
  intro lam hlam beta hbeta hpos hb F hsupp
  have hglobal (x : R3) : finiteCoreSourceEnergy hO hD (beta x) F x ≤
      C*finiteCoreReferenceProfileEnergy hO hD g hg L lam (beta x) F x := by
    by_cases hx : x ∈ K
    · exact hpoint lam hlam x hx (beta x) (hb x hx) F
    · rw [finiteCoreSourceEnergy_eq_zero_of_notMem hO hD K F hsupp x hx]
      exact mul_nonneg hC.le (finiteCoreReferenceProfileEnergy_nonneg hO hD g hg L lam (beta x) (hpos x).le F x)
  have hS := integrable_native_core_source_norm hO hD g hg L lam beta hbeta hpos F
  have hP := integrable_finiteCoreReferenceProfileEnergy hO hD g hg L lam beta hbeta hpos F
  calc
    _ ≤ ∫ x : R3, C*(referenceDensityFamily g L (lam,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L lam (beta x) F x) := by
      apply integral_mono hS (hP.const_mul C)
      intro x
      calc
        _ ≤ referenceDensityFamily g L (lam,x)*(C*finiteCoreReferenceProfileEnergy hO hD g hg L lam (beta x) F x) :=
          mul_le_mul_of_nonneg_left (hglobal x) (referenceDensityFamily_pos g hg L (lam,x)).le
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
