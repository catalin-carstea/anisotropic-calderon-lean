import Calderon.ActualFiniteHarmonicModelAngularProductForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularFinitePairingFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularFinitePairingFunction

def corePointwisePairLinearMap (F G : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    Module.End ℝ (smoothCompactFiniteSphereCore hO hD) →ₗ[ℝ] ℝ where
  toFun T := ⟪T F x,G x⟫_ℝ
  map_add' T U := by
    simp only [LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,inner_add_left]
  map_smul' c T := by
    simp only [LinearMap.smul_apply,Submodule.coe_smul,Pi.smul_apply,real_inner_smul_left,
      RingHom.id_apply,smul_eq_mul]

lemma abs_pair_commutator_finset_sum_le
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (B : κ → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (q : Module.End ℝ (smoothCompactFiniteSphereCore hO hD) →ₗ[ℝ] ℝ)
    (c : ι → ℝ) (d : κ → ℝ) (W : ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ t, |q (commutator (A i) (B j))| ≤ c i*d j*W) :
    |q (commutator (∑ i ∈ s,A i) (∑ j ∈ t,B j))| ≤
      (∑ i ∈ s,c i)*(∑ j ∈ t,d j)*W := by
  rw [commutator_sum_left]
  simp_rw [commutator_sum_right]
  simp only [map_sum]
  calc
    _ ≤ ∑ i ∈ s, |∑ j ∈ t,q (commutator (A i) (B j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t,|q (commutator (A i) (B j))| :=
      Finset.sum_le_sum (fun i hi => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ t,c i*d j*W :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => h i hi j hj))
    _ = _ := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
