import Calderon.ActualFiniteHarmonicModelScalarExpansion

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma coreScalar_add_eq (c d : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) :
    coreScalar hO hD (fun x => c x+d x) (hc.add hd) =
      coreScalar hO hD c hc+coreScalar hO hD d hd := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  exact add_smul (c x) (d x) (F.val x)

lemma coreScalar_neg_eq (c : R3 → ℝ) (hc : ContDiff ℝ ∞ c) :
    coreScalar hO hD (fun x => -c x) hc.neg = -coreScalar hO hD c hc := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  exact neg_smul (c x) (F.val x)

lemma coreScalar_mul_eq (c d : R3 → ℝ) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d) :
    coreScalar hO hD (fun x => c x*d x) (hc.mul hd) =
      coreScalar hO hD c hc*coreScalar hO hD d hd := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  exact mul_smul (c x) (d x) (F.val x)

lemma coreScalarCombination_add {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (c d : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    coreScalarCombination hO hD T (fun i x => c i x+d i x) (fun i => (hc i).add (hd i)) =
      coreScalarCombination hO hD T c hc+coreScalarCombination hO hD T d hd := by
  unfold coreScalarCombination
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coreScalar_add_eq hO hD (c i) (d i) (hc i) (hd i),add_mul]

lemma coreScalarCombination_neg {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i)) :
    coreScalarCombination hO hD T (fun i x => -c i x) (fun i => (hc i).neg) =
      -coreScalarCombination hO hD T c hc := by
  unfold coreScalarCombination
  calc
    _ = ∑ i, -(coreScalar hO hD (c i) (hc i)*T i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coreScalar_neg_eq hO hD (c i) (hc i)]
      rfl
    _ = _ := Finset.sum_neg_distrib (fun i => coreScalar hO hD (c i) (hc i)*T i)

lemma coreScalarCombination_scalar_mul {ι : Type*} [Fintype ι]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (d : R3 → ℝ) (hd : ContDiff ℝ ∞ d) :
    coreScalarCombination hO hD T (fun i x => d x*c i x) (fun i => hd.mul (hc i)) =
      coreScalar hO hD d hd*coreScalarCombination hO hD T c hc := by
  unfold coreScalarCombination
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coreScalar_mul_eq hO hD d (c i) hd (hc i),mul_assoc]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
