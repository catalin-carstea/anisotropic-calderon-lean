import Calderon.ActualCommonSupportCoefficientJetNorm
import Calderon.NativeSmoothBallSobolevFamily
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem exists_commonSupport_smoothBallSobolev_firstJet_bound
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (hcalc : FixedSobolevCalculus) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : H×R3→ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
      (hz : ∀ t x, x ∉ K → g (t,x)=0) (t : H) (M : ℝ), 0 ≤ M →
      (∀ j ≤ k+2, ∀ x:R3, ‖iteratedFDeriv ℝ j g (t,x)‖ ≤ M) →
      ‖smoothBallSobolev k ⟨fun x => g (t,x),SpatialJetFields.contDiff_spatial_slice g hg t⟩‖ ≤ C*M ∧
      ‖fderiv ℝ (fun u => smoothBallSobolev k ⟨fun x => g (u,x),SpatialJetFields.contDiff_spatial_slice g hg u⟩) t‖ ≤ C*M := by
  let one : SmoothData := ⟨fun _ => 1,contDiff_const⟩
  let T : ClosedCoefficientJets (k+1) →L[ℝ] BallSobolev k :=
    (closedCoefficientMultiplierL hcalc k).flip (smoothBallSobolev k one)
  refine ⟨‖T‖+1,by positivity,?_⟩
  intro g hg K hK hz t M hM hBound
  let F := commonSupportClosedCoefficientFamily (k+1) g hg K hK hz
  have hF : ContDiff ℝ ∞ F := contDiff_commonSupportClosedCoefficientFamily (k+1) g hg K hK hz
  have hFn : ‖F t‖ ≤ M := norm_commonSupportClosedCoefficientFamily_le_joint_jets
    (k+1) g hg K hK hz t M hM (fun j hj x => hBound j (by omega) x)
  have hDFn : ‖fderiv ℝ F t‖ ≤ M := norm_fderiv_commonSupportClosedCoefficientFamily_le_joint_jets
    (k+1) g hg K hK hz t M hM hBound
  have hEqual : (T ∘ F) = (fun u => smoothBallSobolev k
      ⟨fun x => g (u,x),SpatialJetFields.contDiff_spatial_slice g hg u⟩) := by
    funext u
    change closedCoefficientMultiplierL hcalc k
      (smoothCoefficientClosureInclusionL (k+1) (commonSupportCoefficientFamily (k+1) g hg K hK hz u))
      (smoothBallSobolev k one) = _
    rw [closedCoefficientMultiplierL_eq_on_smooth,coefficientMultiplier_smoothBallSobolev]
    apply congrArg (smoothBallSobolev k)
    apply Subtype.ext
    funext x
    change coefficientValue (k+1) (commonSupportCoefficientFamily (k+1) g hg K hK hz u) x * 1 = g (u,x)
    rw [mul_one,coefficientValue_commonSupportCoefficientFamily]
  have hDeriv := T.hasFDerivAt.comp t ((hF.differentiable (by simp) t).hasFDerivAt)
  constructor
  · rw [← congrFun hEqual t]
    change ‖T (F t)‖ ≤ (‖T‖+1)*M
    calc
      _ ≤ ‖T‖*‖F t‖ := T.le_opNorm (F t)
      _ ≤ ‖T‖*M := mul_le_mul_of_nonneg_left hFn (norm_nonneg T)
      _ ≤ _ := by nlinarith only [hM]
  · rw [← hEqual,hDeriv.fderiv]
    change ‖T.comp (fderiv ℝ F t)‖ ≤ (‖T‖+1)*M
    calc
      _ ≤ ‖T‖*‖fderiv ℝ F t‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖*M := mul_le_mul_of_nonneg_left hDFn (norm_nonneg T)
      _ ≤ _ := by nlinarith only [hM]

end OAI.AnisotropicCalderon.DirichletFamily
