import Calderon.ActualWeightedNativeFiveSourceMomentHelpers
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- The actual five renormalized differences have a joint order-45 derivative
cap on the fixed cylinder and a closed dilation strip. Its constant is chosen
before the dilation and all radius shrinkage. -/
theorem exists_uniform_joint_iteratedFDeriv45_five_source_bound
    (R1 R2 : Fin 5 → (R3 × ℝ) → ℝ)
    (etaA : ℝ) (hEtaA : 0 < etaA) (U : Set (ℝ × R3))
    (hU : IsOpen U)
    (hStrip : Icc (-etaA) etaA ×ˢ cylinder ⊆ U)
    (hR1 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) (Prod.swap ⁻¹' U))
    (hR2 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) (Prod.swap ⁻¹' U)) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ k : Fin 5, ∀ lam ∈ Icc (-etaA) etaA, ∀ y ∈ cylinder,
        ‖iteratedFDeriv ℝ 45 (fun q : R3 × ℝ => R1 k q-R2 k q) (y,lam)‖ ≤ A := by
  let T : Set (R3 × ℝ) := cylinder ×ˢ Icc (-etaA) etaA
  have hT : IsCompact T := isCompact_native_center_cylinder.prod isCompact_Icc
  have hOpen : IsOpen (Prod.swap ⁻¹' U) := hU.preimage continuous_swap
  have hSubset : T ⊆ Prod.swap ⁻¹' U := by
    intro q hq
    exact hStrip ⟨hq.2,hq.1⟩
  have hFor (k : Fin 5) :
      ∃ C : ℝ, ∀ q ∈ T,
        ‖iteratedFDeriv ℝ 45 (fun q : R3 × ℝ => R1 k q-R2 k q) q‖ ≤ C := by
    have hDiff : ContDiffOn ℝ ∞ (fun q : R3 × ℝ => R1 k q-R2 k q)
        (Prod.swap ⁻¹' U) := (hR1 k).sub (hR2 k)
    have hCont : ContinuousOn
        (iteratedFDeriv ℝ 45 (fun q : R3 × ℝ => R1 k q-R2 k q)) T :=
      (ContinuousOn.continuousOn_iteratedFDeriv hDiff hOpen (by simp)).mono hSubset
    exact hT.exists_bound_of_continuousOn hCont
  choose C hC using hFor
  let A : ℝ := 1 + ∑ k : Fin 5, max (C k) 0
  have hSum : 0 ≤ ∑ k : Fin 5, max (C k) 0 :=
    Finset.sum_nonneg (fun k _ => le_max_right _ _)
  refine ⟨A, by dsimp [A]; linarith, ?_⟩
  intro k lam hLam y hy
  have hTerm : max (C k) 0 ≤ ∑ j : Fin 5, max (C j) 0 :=
    Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ k)
  calc
    ‖iteratedFDeriv ℝ 45 (fun q : R3 × ℝ => R1 k q-R2 k q) (y,lam)‖
        ≤ C k := hC k (y,lam) ⟨hy,hLam⟩
    _ ≤ max (C k) 0 := le_max_left _ _
    _ ≤ A := by dsimp [A]; linarith

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
