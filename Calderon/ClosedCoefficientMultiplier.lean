import Calderon.ClosedCoefficientJets
import Calderon.CoefficientMultiplier
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily

def closedCoefficientMultiplierL (hcalc : FixedSobolevCalculus) (k : ℕ) :
    ClosedCoefficientJets (k+1) →L[ℝ] BallSobolev k →L[ℝ] BallSobolev k :=
  (coefficientMultiplierL hcalc k).extend (smoothCoefficientClosureInclusionL (k+1))

theorem closedCoefficientMultiplierL_eq_on_smooth (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : SmoothCoefficientJets (k+1)) :
    closedCoefficientMultiplierL hcalc k (smoothCoefficientClosureInclusionL (k+1) F) =
      coefficientMultiplier hcalc k F := by
  exact (coefficientMultiplierL hcalc k).extend_eq
    (denseRange_smoothCoefficientClosureInclusionL (k+1))
    ((show Isometry (smoothCoefficientClosureInclusionL (k+1)) from fun _ _ => rfl).isUniformInducing) F

theorem norm_closedCoefficientMultiplierL_apply_le (hcalc : FixedSobolevCalculus) (k : ℕ)
    (F : ClosedCoefficientJets (k+1)) :
    ‖closedCoefficientMultiplierL hcalc k F‖ ≤ sobolevMultiplierBound hcalc k * ‖F‖ := by
  have hm : ∀ G ∈ range (smoothCoefficientClosureInclusionL (k+1)),
      ‖closedCoefficientMultiplierL hcalc k G‖ ≤ sobolevMultiplierBound hcalc k * ‖G‖ := by
    rintro _ ⟨G,rfl⟩
    rw [closedCoefficientMultiplierL_eq_on_smooth,norm_smoothCoefficientClosureInclusionL]
    exact norm_coefficientMultiplier_le hcalc k G
  exact (denseRange_smoothCoefficientClosureInclusionL (k+1)).induction hm
    (isClosed_le (by fun_prop) (by fun_prop)) F

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

theorem contDiff_commonSupport_actual_coefficientMultiplier
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (fun t => coefficientMultiplier hcalc k
      (commonSupportCoefficientFamily (k+1) g hg K hK hz t)) := by
  have he : (fun t => coefficientMultiplier hcalc k
      (commonSupportCoefficientFamily (k+1) g hg K hK hz t)) =
      fun t => closedCoefficientMultiplierL hcalc k
        (commonSupportClosedCoefficientFamily (k+1) g hg K hK hz t) := by
    funext t
    exact (closedCoefficientMultiplierL_eq_on_smooth hcalc k _).symm
  rw [he]
  exact (closedCoefficientMultiplierL hcalc k).contDiff.comp
    (contDiff_commonSupportClosedCoefficientFamily (k+1) g hg K hK hz)
end OAI.AnisotropicCalderon.DirichletFamily
