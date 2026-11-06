import Calderon.ActualFiniteHarmonicModelAngularScalarCommutator
import Calderon.ActualFiniteHarmonicModelAngularFinitePairing

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularScalarProductsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularScalarProductsFunction

lemma coreAngular_scalar_product_eq
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A)
    (c d : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) :
    (coreScalar hO hD c hc*A)*(coreScalar hO hD d hd*B) =
      coreScalar hO hD c hc*coreScalar hO hD d hd*(A*B) := by
  calc
    _ = coreScalar hO hD c hc*(A*coreScalar hO hD d hd)*B := by noncomm_ring
    _ = coreScalar hO hD c hc*(coreScalar hO hD d hd*A)*B := by rw [(hA d hd).eq]
    _ = _ := by noncomm_ring

lemma abs_inner_coreAngular_scalar_product
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hA : ScalarCentral hO hD A)
    (c d : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪((coreScalar hO hD c hc*A)*(coreScalar hO hD d hd*B)) F x,G x⟫_ℝ| =
      |c x| * |d x| * |⟪(A*B) F x,G x⟫_ℝ| := by
  rw [coreAngular_scalar_product_eq hO hD A B hA c d hc hd]
  change |⟪c x • (d x • (A*B) F x),G x⟫_ℝ| = _
  rw [real_inner_smul_left,real_inner_smul_left,abs_mul,abs_mul]
  ring

lemma abs_pair_product_finset_sum_le
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (B : κ → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (q : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) →ₗ[ℝ] ℝ)
    (c : ι → ℝ) (d : κ → ℝ) (W : ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ t, |q (A i*B j)| ≤ c i*d j*W) :
    |q ((∑ i ∈ s,A i)*(∑ j ∈ t,B j))| ≤
      (∑ i ∈ s,c i)*(∑ j ∈ t,d j)*W := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp only [map_sum]
  calc
    _ ≤ ∑ i ∈ s, |∑ j ∈ t,q (A i*B j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t,|q (A i*B j)| :=
      Finset.sum_le_sum (fun i hi => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ t,c i*d j*W :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => h i hi j hj))
    _ = _ := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
