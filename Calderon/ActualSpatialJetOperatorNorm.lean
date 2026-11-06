import Calderon.SpatialJetFields
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.SpatialJetFields

theorem norm_spatialJetField_le_joint_jet
    {H V : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (j : ℕ) (g : H×V → ℝ) (p : H×V) :
    ‖spatialJetField j g p‖ ≤ ‖iteratedFDeriv ℝ j g p‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ H V)

theorem norm_fderiv_spatialJetField_le_joint_succ
    {H V : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (j : ℕ) (g : H×V → ℝ) (hg : ContDiff ℝ ∞ g) (p : H×V) :
    ‖fderiv ℝ (spatialJetField j g) p‖ ≤ ‖iteratedFDeriv ℝ (j+1) g p‖ := by
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin j => H×V) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin j => V) ℝ := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ H V)
  have hT : ‖T‖ ≤ 1 := (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℝ (fun _ : Fin j => ContinuousLinearMap.inr ℝ H V)).trans
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ H V))
  have hD := T.hasFDerivAt.comp p (((hg.iteratedFDeriv_right (m:=∞) (by simp)).differentiable (by simp) p).hasFDerivAt)
  change ‖fderiv ℝ (T ∘ iteratedFDeriv ℝ j g) p‖ ≤ _
  rw [hD.fderiv]
  calc
    _ ≤ ‖T‖*‖fderiv ℝ (iteratedFDeriv ℝ j g) p‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖fderiv ℝ (iteratedFDeriv ℝ j g) p‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = _ := by rw [one_mul,norm_fderiv_iteratedFDeriv]

end OAI.AnisotropicCalderon.SpatialJetFields
