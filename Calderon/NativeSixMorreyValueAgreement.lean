import Calderon.NativeSixMorreyTypedConstructor

/-! EXPANSION.json precedes transport of the entire Morrey AE agreement. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
local instance : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((6 : NNReal) : ENNReal)) := ⟨by norm_num⟩

theorem nativeSixMorreyL_value_ae (u : TauCeti.W1p (volume : Measure R3) ⊤ (6 : ENNReal)) :
    (TauCeti.W1p.value u : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      (nativeSixMorreyL u : R3 → ℝ) := by
  let P := {p : ENNReal // 1 ≤ p}
  let Fiber (p : P) : Type :=
    letI : Fact (1 ≤ p.1) := ⟨p.2⟩
    TauCeti.W1p (volume : Measure R3) ⊤ p.1 →L[ℝ]
      TauCeti.HolderSpace (1 - (Module.finrank ℝ R3 : NNReal) / 6) R3 ℝ
  let Agreement (p : P) (L : Fiber p) : Prop :=
    letI : Fact (1 ≤ p.1) := ⟨p.2⟩
    ∀ v : TauCeti.W1p (volume : Measure R3) ⊤ p.1,
      (TauCeti.W1p.value v : R3 → ℝ) =ᵐ[(volume : Measure R3)] (L v : R3 → ℝ)
  have transportAgreement : ∀ (p q : P) (h : p = q) (L : Fiber p),
      Agreement p L → Agreement q (Eq.mp (congrArg Fiber h) L) := by
    intro p q h L hL
    subst q
    exact hL
  let p0 : P := ⟨((6 : NNReal) : ENNReal),by norm_num⟩
  let p1 : P := ⟨(6 : ENNReal),by norm_num⟩
  have hP : p0 = p1 := by
    apply Subtype.ext
    norm_num [p0,p1]
  let L0 : Fiber p0 := by
    dsimp only [Fiber,p0]
    exact TauCeti.W1p.morreyEmbedding (E := R3) (mu := (volume : Measure R3))
      (p := (6 : NNReal)) (hp := by norm_num [R3])
  have hRaw : Agreement p0 L0 := by
    intro v
    exact TauCeti.W1p.value_ae_eq_morreyEmbedding (E := R3) (mu := (volume : Measure R3))
      (p := (6 : NNReal)) (hp := by norm_num [R3]) (u := v)
  have hNew : Agreement p1 (Eq.mp (congrArg Fiber hP) L0) :=
    transportAgreement p0 p1 hP L0 hRaw
  have hMap : nativeSixMorreyL = Eq.mp (congrArg Fiber hP) L0 := rfl
  rw [hMap]
  exact hNew u

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
