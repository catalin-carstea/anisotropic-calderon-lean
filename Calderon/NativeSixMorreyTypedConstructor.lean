import Calderon.NativeH2BoundedSixRealization

/-! EXPANSION.json precedes whole dependent equality transport of the actual
six-exponent Morrey CLM. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((6 : NNReal) : ENNReal)) := ⟨by
  rw [ENNReal.coe_ofNat]
  norm_num⟩

def nativeSixMorreyL : TauCeti.W1p (volume : Measure R3) ⊤ (6 : ENNReal) →L[ℝ]
    TauCeti.HolderSpace (1 - (Module.finrank ℝ R3 : NNReal) / 6) R3 ℝ := by
  let P := {p : ENNReal // 1 ≤ p}
  let Fiber (p : P) : Type :=
    letI : Fact (1 ≤ p.1) := ⟨p.2⟩
    TauCeti.W1p (volume : Measure R3) ⊤ p.1 →L[ℝ]
      TauCeti.HolderSpace (1 - (Module.finrank ℝ R3 : NNReal) / 6) R3 ℝ
  let p0 : P := ⟨((6 : NNReal) : ENNReal),by norm_num⟩
  let p1 : P := ⟨(6 : ENNReal),by norm_num⟩
  have hP : p0 = p1 := by
    apply Subtype.ext
    norm_num [p0,p1]
  have hRaw : Fiber p0 := by
    dsimp only [Fiber,p0]
    exact TauCeti.W1p.morreyEmbedding (E := R3) (mu := (volume : Measure R3))
      (p := (6 : NNReal)) (hp := by norm_num [R3])
  change Fiber p1
  exact Eq.mp (congrArg Fiber hP) hRaw

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
