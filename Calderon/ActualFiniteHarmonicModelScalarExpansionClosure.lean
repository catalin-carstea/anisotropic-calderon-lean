import Calderon.ActualFiniteHarmonicModelScalarCombinationAlgebra

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma hasCoreScalarExpansionBound_add {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD T A x C)
    (hB : HasCoreScalarExpansionBound hO hD T B x D) :
    HasCoreScalarExpansionBound hO hD T (A+B) x (C+D) := by
  obtain ⟨c,hc,hec,hbc⟩ := hA
  obtain ⟨d,hd,hed,hbd⟩ := hB
  refine ⟨fun i x => c i x+d i x,fun i => (hc i).add (hd i),?_,?_⟩
  · rw [coreScalarCombination_add hO hD T c d hc hd,←hec,←hed]
  · calc
      _ ≤ ∑ i, (|c i x|+|d i x|) := Finset.sum_le_sum (fun i _ => abs_add_le _ _)
      _ = (∑ i, |c i x|)+(∑ i, |d i x|) := Finset.sum_add_distrib
      _ ≤ C+D := add_le_add hbc hbd

lemma hasCoreScalarExpansionBound_neg {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD T A x C) :
    HasCoreScalarExpansionBound hO hD T (-A) x C := by
  obtain ⟨c,hc,he,hb⟩ := hA
  refine ⟨fun i x => -c i x,fun i => (hc i).neg,?_,?_⟩
  · rw [coreScalarCombination_neg hO hD T c hc,←he]
  · simpa only [abs_neg] using hb

lemma hasCoreScalarExpansionBound_sub {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD T A x C)
    (hB : HasCoreScalarExpansionBound hO hD T B x D) :
    HasCoreScalarExpansionBound hO hD T (A-B) x (C+D) := by
  rw [_root_.sub_eq_add_neg A B]
  exact hasCoreScalarExpansionBound_add hO hD T A (-B) x C D hA
    (hasCoreScalarExpansionBound_neg hO hD T B x D hB)

lemma hasCoreScalarExpansionBound_scalar_mul {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD T A x C)
    (d : R3 → ℝ) (hd : ContDiff ℝ ∞ d) :
    HasCoreScalarExpansionBound hO hD T (coreScalar hO hD d hd*A) x (|d x| * C) := by
  obtain ⟨c,hc,he,hb⟩ := hA
  refine ⟨fun i x => d x*c i x,fun i => hd.mul (hc i),?_,?_⟩
  · rw [coreScalarCombination_scalar_mul hO hD T c hc d hd,←he]
  · simp only [abs_mul,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

lemma hasCoreScalarExpansionBound_sum {ι κ : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (s : Finset κ) (A : κ → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (x : R3) (C : κ → ℝ)
    (hA : ∀ i ∈ s, HasCoreScalarExpansionBound hO hD T (A i) x (C i)) :
    HasCoreScalarExpansionBound hO hD T (∑ i ∈ s,A i) x (∑ i ∈ s,C i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using hasCoreScalarExpansionBound_zero hO hD T x
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact hasCoreScalarExpansionBound_add hO hD T _ _ x _ _
      (hA a (Finset.mem_insert_self a s))
      (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)))

lemma coreScalar_const_mul_eq_smul
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (r : ℝ) :
    coreScalar hO hD (fun _ => r) contDiff_const*A = r • A := by
  rfl

lemma hasCoreScalarExpansionBound_smul {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C r : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD T A x C) :
    HasCoreScalarExpansionBound hO hD T (r • A) x (|r| * C) := by
  simpa only [coreScalar_const_mul_eq_smul] using
    hasCoreScalarExpansionBound_scalar_mul hO hD T A x C hA (fun _ => r) contDiff_const

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
