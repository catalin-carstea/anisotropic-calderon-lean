import Calderon.ActualFiniteHarmonicModelAngularGenerators
import Calderon.ActualFiniteHarmonicModelAngularExpansionForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
  ActualModelCommutatorWords ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev quadraticThreehalfFormsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] quadraticThreehalfFormsFunction

lemma coreAngularExpansion_quadratic_threehalf_half_form_bound
    (hF : SphereFischerInner) (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
      coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2) A x C)
    (U V : smoothCompactFiniteSphereCore hO hD) :
    |⟪A U x,V x⟫_ℝ| ≤ (C*(coreAngularGeneratorBound hO hD)^2)*
      ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) U x‖ *
      ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ := by
  obtain ⟨c,hc,he,hcBound⟩ := hA
  let M := coreAngularGeneratorBound hO hD
  let u := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) U x‖
  let v := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖
  have hM : 0 ≤ M := le_trans (by norm_num) (coreAngularGeneratorBound_bounds hO hD).1
  have ht (i : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex) :
      |c i x*⟪(coreAngularGenerator hO hD hF i.1*coreAngularGenerator hO hD hF i.2) U x,V x⟫_ℝ| ≤ |c i x| *(M^2*u*v) := by
    rw [abs_mul]
    have hp := coreAngular_product_threehalf_half_bound hO hD
      (coreAngularGenerator hO hD hF i.1) (coreAngularGeneratorAdjoint hO hD hF i.1)
      (coreAngularGenerator hO hD hF i.2) (coreAngularGeneratorAdjoint hO hD hF i.2)
      M M x (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF i.1 x)
      (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF i.2 x) U V
    exact mul_le_mul_of_nonneg_left (by simpa only [pow_two,mul_assoc] using hp) (abs_nonneg _)
  rw [he]
  dsimp only [coreScalarCombination]
  simp only [LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,sum_inner]
  change |∑ i : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex, ⟪c i x • (coreAngularGenerator hO hD hF i.1*coreAngularGenerator hO hD hF i.2) U x,V x⟫_ℝ| ≤ _
  simp only [real_inner_smul_left]
  calc
    _ ≤ ∑ i, |c i x*⟪(coreAngularGenerator hO hD hF i.1*coreAngularGenerator hO hD hF i.2) U x,V x⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i x| *(M^2*u*v) := Finset.sum_le_sum (fun i _ => ht i)
    _ = (∑ i, |c i x|)*(M^2*u*v) := (Finset.sum_mul _ _ _).symm
    _ ≤ C*(M^2*u*v) := mul_le_mul_of_nonneg_right hcBound (by dsimp only [u,v]; positivity)
    _ = _ := by dsimp only [M,u,v]; ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
