import Calderon.ActualFiniteHarmonicModelGeneratorWordForms
import Calderon.ActualFiniteHarmonicModelAngularScalarCommutator
import Calderon.ActualFiniteHarmonicModelAngularFinitePairing

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularPolynomialCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularPolynomialCommutatorFunction

lemma coreAngular_quadratic_linear_polynomial_commutator_bound
    (hF : SphereFischerInner) {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (i j : ι → CoreAngularGeneratorIndex) (k : κ → CoreAngularGeneratorIndex)
    (c : ι → R3 → ℝ) (d : κ → R3 → ℝ)
    (hc : ∀ a, ContDiff ℝ ∞ (c a)) (hd : ∀ b, ContDiff ℝ ∞ (d b))
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪commutator
      (∑ a ∈ s,coreScalar hO hD (c a) (hc a)*
        (coreAngularGenerator hO hD hF (i a)*coreAngularGenerator hO hD hF (j a)))
      (∑ b ∈ t,coreScalar hO hD (d b) (hd b)*coreAngularGenerator hO hD hF (k b)) F x,G x⟫_ℝ| ≤
      (∑ a ∈ s,|c a x|)*(∑ b ∈ t,|d b x|)*
        ((8*(coreAngularGeneratorBound hO hD)^2)*
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  let A (a : ι) := coreScalar hO hD (c a) (hc a)*
    (coreAngularGenerator hO hD hF (i a)*coreAngularGenerator hO hD hF (j a))
  let B (b : κ) := coreScalar hO hD (d b) (hd b)*coreAngularGenerator hO hD hF (k b)
  let q := corePointwisePairLinearMap hO hD F G x
  apply abs_pair_commutator_finset_sum_le hO hD s t A B q
    (fun a => |c a x|) (fun b => |d b x|)
  intro a ha b hb
  change |⟪commutator (A a) (B b) F x,G x⟫_ℝ| ≤ _
  dsimp only [A,B]
  rw [abs_inner_coreAngular_scalar_commutator hO hD _ _
    (scalarCentral_mul hO hD _ _ (scalarCentral_coreAngularGenerator hO hD hF (i a))
      (scalarCentral_coreAngularGenerator hO hD hF (j a)))
    (scalarCentral_coreAngularGenerator hO hD hF (k b)) (c a) (d b) (hc a) (hd b) F G x]
  exact mul_le_mul_of_nonneg_left
    (coreAngularGenerator_quadratic_linear_commutator_bound hO hD hF (i a) (j a) (k b) F G x)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

lemma coreAngular_quadratic_quadratic_polynomial_commutator_bound
    (hF : SphereFischerInner) {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (i j : ι → CoreAngularGeneratorIndex) (k l : κ → CoreAngularGeneratorIndex)
    (c : ι → R3 → ℝ) (d : κ → R3 → ℝ)
    (hc : ∀ a, ContDiff ℝ ∞ (c a)) (hd : ∀ b, ContDiff ℝ ∞ (d b))
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪commutator
      (∑ a ∈ s,coreScalar hO hD (c a) (hc a)*
        (coreAngularGenerator hO hD hF (i a)*coreAngularGenerator hO hD hF (j a)))
      (∑ b ∈ t,coreScalar hO hD (d b) (hd b)*(coreAngularGenerator hO hD hF (k b)*coreAngularGenerator hO hD hF (l b))) F x,G x⟫_ℝ| ≤
      (∑ a ∈ s,|c a x|)*(∑ b ∈ t,|d b x|)*
        ((16*(coreAngularGeneratorBound hO hD)^3)*
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  let A (a : ι) := coreScalar hO hD (c a) (hc a)*
    (coreAngularGenerator hO hD hF (i a)*coreAngularGenerator hO hD hF (j a))
  let B (b : κ) := coreScalar hO hD (d b) (hd b)*(coreAngularGenerator hO hD hF (k b)*coreAngularGenerator hO hD hF (l b))
  let q := corePointwisePairLinearMap hO hD F G x
  apply abs_pair_commutator_finset_sum_le hO hD s t A B q
    (fun a => |c a x|) (fun b => |d b x|)
  intro a ha b hb
  change |⟪commutator (A a) (B b) F x,G x⟫_ℝ| ≤ _
  dsimp only [A,B]
  rw [abs_inner_coreAngular_scalar_commutator hO hD _ _
    (scalarCentral_mul hO hD _ _ (scalarCentral_coreAngularGenerator hO hD hF (i a))
      (scalarCentral_coreAngularGenerator hO hD hF (j a)))
    (scalarCentral_mul hO hD _ _ (scalarCentral_coreAngularGenerator hO hD hF (k b))
        (scalarCentral_coreAngularGenerator hO hD hF (l b))) (c a) (d b) (hc a) (hd b) F G x]
  exact mul_le_mul_of_nonneg_left
    (coreAngularGenerator_quadratic_quadratic_commutator_bound hO hD hF (i a) (j a) (k b) (l b) F G x)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
