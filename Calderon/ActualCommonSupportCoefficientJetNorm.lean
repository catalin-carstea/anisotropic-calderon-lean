import Calderon.ActualSpatialJetOperatorNorm
import Calderon.ClosedCoefficientJets
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.DirichletFamily
open SpatialJetFields BoundedParameterSmoothness

def closedCoefficientJetEvaluationL (r : ℕ) (j : Fin (r+1)) (x : R3) :
    ClosedCoefficientJets r →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j.val => R3) ℝ :=
  ((BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousLinearMap.proj j)).comp
    (smoothCoefficientJetSubmodule r).topologicalClosure.subtypeL

theorem norm_commonSupportClosedCoefficientFamily_le_joint_jets
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (r : ℕ) (g : H×R3→ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x)=0) (t : H) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ j ≤ r, ∀ x:R3, ‖iteratedFDeriv ℝ j g (t,x)‖ ≤ M) :
    ‖commonSupportClosedCoefficientFamily r g hg K hK hz t‖ ≤ M := by
  change ‖(commonSupportCoefficientFamily r g hg K hK hz t).val‖ ≤ M
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro j
  apply (BoundedContinuousFunction.norm_le hM).mpr
  intro x
  rw [commonSupportCoefficientFamily_jet,← spatialJetField_eq_iteratedFDeriv j.val g hg t x]
  exact (norm_spatialJetField_le_joint_jet j.val g (t,x)).trans (hBound j.val (by omega) x)

theorem norm_fderiv_commonSupportClosedCoefficientFamily_le_joint_jets
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (r : ℕ) (g : H×R3→ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x)=0) (t : H) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ j ≤ r+1, ∀ x:R3, ‖iteratedFDeriv ℝ j g (t,x)‖ ≤ M) :
    ‖fderiv ℝ (commonSupportClosedCoefficientFamily r g hg K hK hz) t‖ ≤ M := by
  let F := commonSupportClosedCoefficientFamily r g hg K hK hz
  have hF : ContDiff ℝ ∞ F := contDiff_commonSupportClosedCoefficientFamily r g hg K hK hz
  apply (fderiv ℝ F t).opNorm_le_bound hM
  intro h
  change ‖(fderiv ℝ F t h).val‖ ≤ M*‖h‖
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (norm_nonneg h))).mpr
  intro j
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hM (norm_nonneg h))).mpr
  intro x
  let ev := closedCoefficientJetEvaluationL r j x
  have hFD := ev.hasFDerivAt.comp t ((hF.differentiable (by simp) t).hasFDerivAt)
  have hFunction : (fun z => ev (F z)) = (fun z => spatialJetField j.val g (z,x)) := by
    funext z
    change (commonSupportCoefficientFamily r g hg K hK hz z).val j x = spatialJetField j.val g (z,x)
    rw [commonSupportCoefficientFamily_jet,spatialJetField_eq_iteratedFDeriv j.val g hg z x]
  change HasFDerivAt (fun z => ev (F z)) (ev.comp (fderiv ℝ F t)) t at hFD
  rw [hFunction] at hFD
  have hPD := hasFDerivAt_base_slice (spatialJetField j.val g)
    ((contDiff_spatialJetField j.val g hg).differentiable (by simp)) t x
  have hEval := congrArg (fun A => A h) (hFD.unique hPD)
  change ‖(ev.comp (fderiv ℝ F t)) h‖ ≤ M*‖h‖
  rw [hEval]
  have hPart : ‖basePartial (spatialJetField j.val g) (t,x)‖ ≤ M := by
    calc
      _ ≤ ‖fderiv ℝ (spatialJetField j.val g) (t,x)‖*‖ContinuousLinearMap.inl ℝ H R3‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (spatialJetField j.val g) (t,x)‖*1 := mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ H R3) (norm_nonneg _)
      _ ≤ ‖iteratedFDeriv ℝ (j.val+1) g (t,x)‖ := by rw [mul_one];exact norm_fderiv_spatialJetField_le_joint_succ j.val g hg (t,x)
      _ ≤ M := hBound (j.val+1) (by omega) x
  exact ((basePartial (spatialJetField j.val g) (t,x)).le_opNorm h).trans
    (mul_le_mul_of_nonneg_right hPart (norm_nonneg h))

end OAI.AnisotropicCalderon.DirichletFamily
