import Calderon.ActualFiniteHarmonicModelScalarCombinationAlgebra

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

lemma coreScalarCombination_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (U : κ → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hT : ∀ i, ScalarCentral hO hD (T i))
    (c : ι → R3 → ℝ) (d : κ → R3 → ℝ)
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (hd : ∀ j, ContDiff ℝ ∞ (d j)) :
    coreScalarCombination hO hD (fun p : ι × κ => T p.1*U p.2)
      (fun p x => c p.1 x*d p.2 x) (fun p => (hc p.1).mul (hd p.2)) =
      coreScalarCombination hO hD T c hc*coreScalarCombination hO hD U d hd := by
  unfold coreScalarCombination
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coreScalar_mul_eq hO hD (c i) (d j) (hc i) (hd j)]
  exact (coreAngular_scalar_product_eq hO hD (T i) (U j) (hT i) (c i) (d j) (hc i) (hd j)).symm

lemma hasCoreScalarExpansionBound_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (U : κ → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hT : ∀ i, ScalarCentral hO hD (T i))
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD T A x C)
    (hB : HasCoreScalarExpansionBound hO hD U B x D) :
    HasCoreScalarExpansionBound hO hD (fun p : ι × κ => T p.1*U p.2) (A*B) x (C*D) := by
  have hC := hasCoreScalarExpansionBound_nonneg hO hD T A x C hA
  obtain ⟨c,hc,hec,hbc⟩ := hA
  obtain ⟨d,hd,hed,hbd⟩ := hB
  refine ⟨fun p x => c p.1 x*d p.2 x,fun p => (hc p.1).mul (hd p.2),?_,?_⟩
  · rw [coreScalarCombination_product hO hD T U hT c d hc hd,←hec,←hed]
  · simp only [Fintype.sum_prod_type,abs_mul]
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul]
    exact mul_le_mul hbc hbd (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hC

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
