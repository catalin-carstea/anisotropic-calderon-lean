import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient

/-! EXPANSION.json precedes derived literal radial collar cutoff data. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric TopologicalSpace
open scoped Gradient Topology
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier

lemma exists_boundaryCollarCutoff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (eta : E → ℝ) (M : ℝ), ContDiff ℝ ∞ eta ∧ 0 ≤ M ∧
      (∀ x, |eta x| ≤ M) ∧ (∀ x, ‖∇ eta x‖ ≤ M) ∧
      (∀ x ∈ closedBall (0 : E) a, eta x = 0) ∧
      (∀ x ∉ ball (0 : E) b, eta x = 1) ∧
      tsupport eta ⊆ (ball (0 : E) a)ᶜ := by
  have hSub : closedBall (0 : E) a ⊆ ball (0 : E) b := by
    intro x hx
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hab)
  obtain ⟨chi,C,hchi,hRange,hOne,hCompact,hSupport,hC,hValue,hGrad⟩ :=
    (isCompact_closedBall (0 : E) a).exists_contDiff_cutoff_with_bounds isOpen_ball hSub
  let eta : E → ℝ := fun x => 1-chi x
  let M : ℝ := max 1 C
  have hEta : ContDiff ℝ ∞ eta := contDiff_const.sub hchi
  have hZero : ∀ x ∈ closedBall (0 : E) a, eta x = 0 := by
    intro x hx
    have hMem : x ∈ chi ⁻¹' ({1} : Set ℝ) :=
      interior_subset (s := chi ⁻¹' ({1} : Set ℝ)) (hOne hx)
    have hc : chi x = 1 := by
      simpa only [Set.mem_preimage,Set.mem_singleton_iff] using hMem
    simp only [eta,hc,sub_self]
  have hOut : ∀ x ∉ ball (0 : E) b, eta x = 1 := by
    intro x hx
    have hNot : x ∉ tsupport chi := fun h => hx (hSupport h)
    simp only [eta,image_eq_zero_of_notMem_tsupport hNot,sub_zero]
  refine ⟨eta,M,hEta,zero_le_one.trans (le_max_left _ _),?_,?_,hZero,hOut,?_⟩
  · intro x
    have hchiX : chi x ∈ Icc (0 : ℝ) 1 := hRange (mem_range_self x)
    have hNonneg : 0 ≤ 1-chi x := sub_nonneg.mpr hchiX.2
    have hBound : |eta x| ≤ 1 := by
      dsimp only [eta]
      rw [abs_of_nonneg hNonneg]
      exact sub_le_self (1 : ℝ) hchiX.1
    exact hBound.trans (le_max_left _ _)
  · intro x
    rw [TauCeti.norm_gradient_eq_norm_fderiv]
    change ‖fderiv ℝ (fun y : E => 1-chi y) x‖ ≤ M
    rw [fderiv_const_sub,norm_neg,← TauCeti.norm_gradient_eq_norm_fderiv]
    exact (hGrad x).trans (le_max_right _ _)
  · change closure (Function.support eta) ⊆ (ball (0 : E) a)ᶜ
    apply closure_minimal ?_ isOpen_ball.isClosed_compl
    intro x hx hBall
    exact hx (hZero x (ball_subset_closedBall hBall))

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.exists_boundaryCollarCutoff
