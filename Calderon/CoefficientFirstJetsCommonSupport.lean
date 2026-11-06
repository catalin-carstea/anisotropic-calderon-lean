import Calderon.NativeCoefficientH1ProductDerivative
import Calderon.ClosedCoefficientMultiplier

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

theorem smoothCoefficientJets_eq_of_coefficientValue_eq (r : ℕ)
    (F G : SmoothCoefficientJets r) (h : coefficientValue r F = coefficientValue r G) : F = G := by
  apply Subtype.ext
  funext j
  apply BoundedContinuousFunction.ext
  intro x
  rw [coefficientJet_eq_iteratedFDeriv,coefficientJet_eq_iteratedFDeriv,h]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem coefficientFirstJets_commonSupportCoefficientFamily
    (g : P × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ p x, x ∉ K → g (p,x) = 0) (p : P) :
    coefficientFirstJets (commonSupportCoefficientFamily 2 g hg K hK hz p) =
      commonSupportCoefficientFamily 1 g hg K hK hz p := by
  apply smoothCoefficientJets_eq_of_coefficientValue_eq 1
  funext x
  rw [coefficientValue_coefficientFirstJets]
  rw [coefficientValue_commonSupportCoefficientFamily,coefficientValue_commonSupportCoefficientFamily]

theorem contDiff_coefficientMultiplier_coefficientFirstJets_commonSupport
    [FiniteDimensional ℝ P] (hcalc : FixedSobolevCalculus)
    (g : P × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ p x, x ∉ K → g (p,x) = 0) :
    ContDiff ℝ ∞ (fun p : P => coefficientMultiplier hcalc 0
      (coefficientFirstJets (commonSupportCoefficientFamily 2 g hg K hK hz p))) := by
  have he : (fun p : P => coefficientMultiplier hcalc 0
      (coefficientFirstJets (commonSupportCoefficientFamily 2 g hg K hK hz p))) =
      fun p : P => coefficientMultiplier hcalc 0 (commonSupportCoefficientFamily 1 g hg K hK hz p) := by
    funext p
    rw [coefficientFirstJets_commonSupportCoefficientFamily]
  rw [he]
  exact contDiff_commonSupport_actual_coefficientMultiplier hcalc 0 g hg K hK hz

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
