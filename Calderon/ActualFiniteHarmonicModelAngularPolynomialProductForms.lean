import Calderon.ActualFiniteHarmonicModelAngularScalarProducts

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularPolynomialProductFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularPolynomialProductFunction

lemma coreAngular_linear_quadratic_polynomial_product_bound
    (hF : SphereFischerInner) {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (i : ι → CoreAngularGeneratorIndex) (j k : κ → CoreAngularGeneratorIndex)
    (c : ι → R3 → ℝ) (d : κ → R3 → ℝ)
    (hc : ∀ a, ContDiff ℝ ∞ (c a)) (hd : ∀ b, ContDiff ℝ ∞ (d b))
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪((∑ a ∈ s,coreScalar hO hD (c a) (hc a)*coreAngularGenerator hO hD hF (i a))*
      (∑ b ∈ t,coreScalar hO hD (d b) (hd b)*(coreAngularGenerator hO hD hF (j b)*coreAngularGenerator hO hD hF (k b)))) F x,G x⟫_ℝ| ≤
      (∑ a ∈ s,|c a x|)*(∑ b ∈ t,|d b x|)*
        ((coreAngularGeneratorBound hO hD)^3*
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  let A (a : ι) := coreScalar hO hD (c a) (hc a)*coreAngularGenerator hO hD hF (i a)
  let B (b : κ) := coreScalar hO hD (d b) (hd b)*(coreAngularGenerator hO hD hF (j b)*coreAngularGenerator hO hD hF (k b))
  let q := corePointwisePairLinearMap hO hD F G x
  apply abs_pair_product_finset_sum_le hO hD s t A B q (fun a => |c a x|) (fun b => |d b x|)
  intro a ha b hb
  change |⟪(A a*B b) F x,G x⟫_ℝ| ≤ _
  dsimp only [A,B]
  rw [abs_inner_coreAngular_scalar_product hO hD _ _
    (scalarCentral_coreAngularGenerator hO hD hF (i a)) (c a) (d b) (hc a) (hd b) F G x]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have ht := coreAngular_triple_threehalf_bound hO hD _ _ _ _ _ _ _ _ _ x
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (i a) x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (j b) x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (k b) x) F G
  simpa only [mul_assoc,pow_succ,pow_zero,one_mul] using ht

lemma coreAngular_quadratic_linear_polynomial_product_bound
    (hF : SphereFischerInner) {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (i j : ι → CoreAngularGeneratorIndex) (k : κ → CoreAngularGeneratorIndex)
    (c : ι → R3 → ℝ) (d : κ → R3 → ℝ)
    (hc : ∀ a, ContDiff ℝ ∞ (c a)) (hd : ∀ b, ContDiff ℝ ∞ (d b))
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪((∑ a ∈ s,coreScalar hO hD (c a) (hc a)*(coreAngularGenerator hO hD hF (i a)*coreAngularGenerator hO hD hF (j a)))*
      (∑ b ∈ t,coreScalar hO hD (d b) (hd b)*coreAngularGenerator hO hD hF (k b))) F x,G x⟫_ℝ| ≤
      (∑ a ∈ s,|c a x|)*(∑ b ∈ t,|d b x|)*
        ((coreAngularGeneratorBound hO hD)^3*
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
          ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  let A (a : ι) := coreScalar hO hD (c a) (hc a)*(coreAngularGenerator hO hD hF (i a)*coreAngularGenerator hO hD hF (j a))
  let B (b : κ) := coreScalar hO hD (d b) (hd b)*coreAngularGenerator hO hD hF (k b)
  let q := corePointwisePairLinearMap hO hD F G x
  apply abs_pair_product_finset_sum_le hO hD s t A B q (fun a => |c a x|) (fun b => |d b x|)
  intro a ha b hb
  change |⟪(A a*B b) F x,G x⟫_ℝ| ≤ _
  dsimp only [A,B]
  rw [abs_inner_coreAngular_scalar_product hO hD _ _
    (scalarCentral_mul hO hD _ _ (scalarCentral_coreAngularGenerator hO hD hF (i a))
      (scalarCentral_coreAngularGenerator hO hD hF (j a))) (c a) (d b) (hc a) (hd b) F G x]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have ht := coreAngular_triple_threehalf_bound hO hD _ _ _ _ _ _ _ _ _ x
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (i a) x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (j a) x)
    (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF (k b) x) F G
  simpa only [mul_assoc,pow_succ,pow_zero,one_mul] using ht

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
