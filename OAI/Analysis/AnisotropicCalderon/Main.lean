-- Main isolated materialization under FINAL-MAIN-HANDOFF-NOV04-v001; Transfer draft retained verbatim.
-- BEFORE-CODE ONLY: requires actual reviewed and admitted original coercivity.
import Calderon.ActualCurrentMainConditionalTransferIntegration
import Calderon.ActualOriginalTwoDirectionPhysicalCoercivity

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon

theorem main (g₁ g₂ : MatrixField)
    (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hΛ : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g₁ f = minimalEnergy g₂ f) :
    ∃ Φ : R3 ≃ R3, IsIsometryFixingExterior Φ g₁ g₂ := by
  have hCoercive :
      MixedKernelConstructionTask.TwoSidedOriginalChosenCoverFinitePhysicalCoercivity g₁ g₂ :=
    MixedKernelConstructionTask.exists_two_sided_original_chosen_cover_finite_physical_coercivity g₁ g₂
  exact MainAssemblyWithTransferProducer.exists_isometryFixingExterior_of_chosen_cover_finite_physical_coercivity
    g₁ g₂ hg₁ hg₂ hΛ hCoercive

end OAI.AnisotropicCalderon
