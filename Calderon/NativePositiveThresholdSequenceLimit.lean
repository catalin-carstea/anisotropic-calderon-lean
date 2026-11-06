import Calderon.NativePositiveThresholdComponentLimits

/-! EXPANSION.json precedes actual positive-threshold native graph-norm convergence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.EnergyBridge
attribute [local irreducible] TauCeti.W1p.posPartAbove TauCeti.W1p.posPart

theorem tendsto_nativeH1_posPartAbove_one_div_add (u : BallH1) :
    Tendsto (fun n : ℕ => TauCeti.W1p.posPartAbove
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity) u) atTop
      (𝓝 (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u)) := by
  exact TauCeti.W1p.tendsto_iff_value_gradient.mpr
    ⟨tendsto_nativeH1_posPartAbove_value_one_div_add u,
      tendsto_nativeH1_posPartAbove_gradient_one_div_add u⟩

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tendsto_nativeH1_posPartAbove_one_div_add
