import Calderon.RadiusGraphFirstJetBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

/-- Exact derivative cap for the finite-dimensional tuple used by the regular moving remainder. -/
theorem norm_fderiv_radiusJetGraph_pullback_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) → V)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (M : ℝ)
    (hF : DifferentiableAt ℝ F ((q,(y,R y)),fderiv ℝ R y))
    (hR : DifferentiableAt ℝ R y) (hDR : DifferentiableAt ℝ (fderiv ℝ R) y)
    (hFbound : ‖fderiv ℝ F ((q,(y,R y)),fderiv ℝ R y)‖ ≤ M)
    (hRbound : ‖fderiv ℝ R y‖ ≤ 1)
    (hDRbound : ‖fderiv ℝ (fderiv ℝ R) y‖ ≤ 1) :
    ‖fderiv ℝ (fun z => F ((q,(z,R z)),fderiv ℝ R z)) y‖ ≤ M := by
  let T : R3 →L[ℝ] ((ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) :=
    ((0 : R3 →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ R3).prod (fderiv ℝ R y))).prod
      (fderiv ℝ (fderiv ℝ R) y)
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    have hRv : ‖fderiv ℝ R y v‖ ≤ ‖v‖ :=
      ((fderiv ℝ R y).le_opNorm v).trans
        ((mul_le_mul_of_nonneg_right hRbound (norm_nonneg v)).trans_eq (one_mul _))
    have hDRv : ‖fderiv ℝ (fderiv ℝ R) y v‖ ≤ ‖v‖ :=
      ((fderiv ℝ (fderiv ℝ R) y).le_opNorm v).trans
        ((mul_le_mul_of_nonneg_right hDRbound (norm_nonneg v)).trans_eq (one_mul _))
    change ‖(((0:ℝ),(v,fderiv ℝ R y v)),fderiv ℝ (fderiv ℝ R) y v)‖ ≤ 1*‖v‖
    simp only [Prod.norm_def,norm_zero,one_mul]
    exact max_le (max_le (norm_nonneg v) (max_le le_rfl hRv)) hDRv
  have hGraph : HasFDerivAt (fun z => ((q,(z,R z)),fderiv ℝ R z)) T y :=
    ((hasFDerivAt_const q y).prodMk ((hasFDerivAt_id y).prodMk hR.hasFDerivAt)).prodMk hDR.hasFDerivAt
  have hComp : fderiv ℝ (fun z => F ((q,(z,R z)),fderiv ℝ R z)) y =
      (fderiv ℝ F ((q,(y,R y)),fderiv ℝ R y)).comp T := (hF.hasFDerivAt.comp y hGraph).fderiv
  rw [hComp]
  calc
    _ ≤ ‖fderiv ℝ F ((q,(y,R y)),fderiv ℝ R y)‖*‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ F ((q,(y,R y)),fderiv ℝ R y)‖*1 := mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    _ = ‖fderiv ℝ F ((q,(y,R y)),fderiv ℝ R y)‖ := mul_one _
    _ ≤ M := hFbound

end OAI.AnisotropicCalderon.ConnectionError
