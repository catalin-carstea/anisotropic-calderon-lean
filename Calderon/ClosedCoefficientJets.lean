import Calderon.CoefficientJetFamily
import Calderon.ClosedSubmoduleSmoothness

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily

abbrev ClosedCoefficientJets (r : ℕ) := ↥(smoothCoefficientJetSubmodule r).topologicalClosure

instance instCompleteSpaceClosedCoefficientJets (r : ℕ) : CompleteSpace (ClosedCoefficientJets r) := by
  unfold ClosedCoefficientJets
  infer_instance

def smoothCoefficientClosureInclusionL (r : ℕ) :
    SmoothCoefficientJets r →L[ℝ] ClosedCoefficientJets r :=
  (smoothCoefficientJetSubmodule r).subtypeL.codRestrict
    (smoothCoefficientJetSubmodule r).topologicalClosure
    (fun F => (smoothCoefficientJetSubmodule r).le_topologicalClosure F.property)

theorem norm_smoothCoefficientClosureInclusionL (r : ℕ) (F : SmoothCoefficientJets r) :
    ‖smoothCoefficientClosureInclusionL r F‖ = ‖F‖ := rfl

theorem denseRange_smoothCoefficientClosureInclusionL (r : ℕ) :
    DenseRange (smoothCoefficientClosureInclusionL r) := by
  change DenseRange (Set.inclusion (smoothCoefficientJetSubmodule r).le_topologicalClosure)
  apply (denseRange_inclusion_iff (smoothCoefficientJetSubmodule r).le_topologicalClosure).mpr
  rw [Submodule.topologicalClosure_coe]

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

def commonSupportClosedCoefficientFamily (r : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) : ClosedCoefficientJets r :=
  smoothCoefficientClosureInclusionL r (commonSupportCoefficientFamily r g hg K hK hz t)

theorem commonSupportClosedCoefficientFamily_val (r : ℕ) (g : H × R3 → ℝ)
    (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) (t : H) :
    (commonSupportClosedCoefficientFamily r g hg K hK hz t).val =
      (commonSupportCoefficientFamily r g hg K hK hz t).val := rfl

theorem contDiff_commonSupportClosedCoefficientFamily [FiniteDimensional ℝ H]
    (r : ℕ) (g : H × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → g (t,x) = 0) :
    ContDiff ℝ ∞ (commonSupportClosedCoefficientFamily r g hg K hK hz) := by
  apply contDiff_infty_closed_submodule _
    (smoothCoefficientJetSubmodule r).isClosed_topologicalClosure
  exact contDiff_commonSupportCoefficientFamily_val r g hg K hK hz
end OAI.AnisotropicCalderon.DirichletFamily
