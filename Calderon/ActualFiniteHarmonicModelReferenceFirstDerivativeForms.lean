import Calderon.ActualFiniteHarmonicModelReferenceFirstDerivativeExpansion
import Calderon.ActualFiniteHarmonicModelAngularExpansionForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualModelCommutatorWords ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev referenceFirstDerivativeFormsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] referenceFirstDerivativeFormsFunction

lemma coreAngularExpansion_linear_half_form_bound
    (hF : SphereFischerInner) (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF) A x C)
    (U V : smoothCompactFiniteSphereCore hO hD) :
    |⟪A U x,V x⟫_ℝ| ≤ (C*coreAngularGeneratorBound hO hD)*
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ := by
  obtain ⟨c,hc,he,hcBound⟩ := hA
  let M := coreAngularGeneratorBound hO hD
  let u := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖
  let v := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖
  have hM : 0 ≤ M := le_trans (by norm_num) (coreAngularGeneratorBound_bounds hO hD).1
  have ht (i : CoreAngularGeneratorIndex) :
      |c i x*⟪coreAngularGenerator hO hD hF i U x,V x⟫_ℝ| ≤ |c i x| *(M*u*v) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF i x).2.2.1 U V) (abs_nonneg _)
  rw [he]
  change |⟪(∑ i, coreScalar hO hD (c i) (hc i)*coreAngularGenerator hO hD hF i) U x,V x⟫_ℝ| ≤ _
  simp only [LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,sum_inner]
  change |∑ i, ⟪c i x • coreAngularGenerator hO hD hF i U x,V x⟫_ℝ| ≤ _
  simp only [real_inner_smul_left]
  calc
    _ ≤ ∑ i, |c i x*⟪coreAngularGenerator hO hD hF i U x,V x⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i x| *(M*u*v) := Finset.sum_le_sum (fun i _ => ht i)
    _ = (∑ i, |c i x|)*(M*u*v) := (Finset.sum_mul _ _ _).symm
    _ ≤ C*(M*u*v) := mul_le_mul_of_nonneg_right hcBound (by dsimp only [u,v]; positivity)
    _ = _ := by dsimp only [M,u,v]; ring

theorem exists_nativeReferenceFirst_coefficientDerivative_uniform_half_forms
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ R : ℝ, ∀ p : ℕ, ∀ hδ : 0 < δ, ∀ hR : 0 < R,
      ∀ x ∈ K, ∀ j k : Fin 3, ∀ U V : smoothCompactFiniteSphereCore hO hD,
      |⟪coefficientDerivative (coreDirectionalDerivative hO hD (coordinateDirection k))
        (nativeReferenceFirstCoefficient hO hD hF g hg L lam δ R p hδ hR j) U x,V x⟫_ℝ| ≤
        C*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ := by
  obtain ⟨C,hC,hE⟩ := exists_nativeReferenceFirst_coefficientDerivative_uniform_linear_expansion hO hD hF g hg L K hK
  have hM : 0 < coreAngularGeneratorBound hO hD := by
    have ht := (coreAngularGeneratorBound_bounds hO hD).1
    linarith
  refine ⟨C*coreAngularGeneratorBound hO hD,mul_pos hC hM,?_⟩
  intro lam hlam δ R p hδ hR x hx j k U V
  exact coreAngularExpansion_linear_half_form_bound hO hD hF _ x C
    (hE lam hlam δ R p hδ hR x hx j k) U V

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
