import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Compactness.Compact

/-! Compact norm-zero tube; no completeness is required. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped Topology
namespace OAI.AnisotropicCalderon.ConnectionError

/-- A continuous zero slice over a compact set has one closed signed norm tube. -/
theorem exists_signed_radius_of_compact_zero_slice
    {P V : Type*} [TopologicalSpace P] [NormedAddCommGroup V]
    (H : P × ℝ → V) (hH : Continuous H) (K : Set P) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η)
    (hzero : ∀ p ∈ K, H (p,0) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ p ∈ K, ∀ r : ℝ, |r| ≤ δ → ‖H (p,r)‖ < η := by
  have ho : IsOpen {p : P × ℝ | ‖H p‖ < η} :=
    isOpen_lt hH.norm continuous_const
  have hsub : K ×ˢ ({0} : Set ℝ) ⊆ {p : P × ℝ | ‖H p‖ < η} := by
    intro p hp
    have hr : p.2 = 0 := mem_singleton_iff.mp hp.2
    change ‖H (p.1,p.2)‖ < η
    rw [hr,hzero p.1 hp.1,norm_zero]
    exact hη
  obtain ⟨U,W,_,hW,hKU,h0W,hUW⟩ :=
    generalized_tube_lemma hK isCompact_singleton ho hsub
  obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp hW 0 (h0W (mem_singleton (0 : ℝ)))
  refine ⟨min ε (a/2),lt_min hε (half_pos ha),min_le_left _ _,?_⟩
  intro p hp r hr
  have hrW : r ∈ W := by
    apply hball
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs]
    exact lt_of_le_of_lt (hr.trans (min_le_right _ _)) (half_lt_self ha)
  exact hUW (a := (p,r)) ⟨hKU hp,hrW⟩

end OAI.AnisotropicCalderon.ConnectionError
