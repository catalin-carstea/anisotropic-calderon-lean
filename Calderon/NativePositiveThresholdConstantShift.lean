import Calderon.SmoothSobolevBridge
import TauCeti.Analysis.Sobolev.W1p.LevelSet

/-! EXPANSION.json precedes the actual threshold/constant-shift identity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.EnergyBridge
attribute [local irreducible] TauCeti.W1p.posPartAbove TauCeti.W1p.posPart smoothSobolev

theorem nativeH1_posPartAbove_eq_posPart_sub_constant
    (u : BallH1) (ε : ℝ) (hε : 0 ≤ ε) :
    TauCeti.W1p.posPartAbove (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hε u =
      TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        (u - ε • smoothSobolev ⟨fun _ : R3 => (1 : ℝ),contDiff_const⟩) := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  let hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  let e : SmoothData := ⟨fun _ : R3 => (1 : ℝ),contDiff_const⟩
  let v : BallH1 := u - ε • smoothSobolev e
  have hSplit : TauCeti.W1p.value v = TauCeti.W1p.value u - ε • TauCeti.W1p.value (smoothSobolev e) := by
    dsimp only [v]
    simp only [← TauCeti.W1p.valueL_apply,map_sub,map_smul]
  have hAbove : TauCeti.W1p.value (TauCeti.W1p.posPartAbove hp hε u) =ᵐ[μ]
      (fun x => max (TauCeti.W1p.value u x - ε) 0) :=
    TauCeti.W1p.value_posPartAbove_ae hp hε u
  have hPos : TauCeti.W1p.value (TauCeti.W1p.posPart hp v) =ᵐ[μ]
      (fun x => max (TauCeti.W1p.value v x) 0) := by
    rw [TauCeti.W1p.value_posPart]
    exact Lp.coeFn_posPart _
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [hAbove,hPos,
    Lp.coeFn_sub (TauCeti.W1p.value u) (ε • TauCeti.W1p.value (smoothSobolev e)),
    Lp.coeFn_smul ε (TauCeti.W1p.value (smoothSobolev e)),value_smoothSobolev_ae e]
    with x hAboveX hPosX hSub hSmul he
  have hEval : TauCeti.W1p.value v x =
      (TauCeti.W1p.value u - ε • TauCeti.W1p.value (smoothSobolev e)) x :=
    congrArg (fun F : Lp ℝ 2 μ => F x) hSplit
  have hShift : TauCeti.W1p.value v x = TauCeti.W1p.value u x - ε := by
    rw [hEval,hSub,Pi.sub_apply,hSmul,Pi.smul_apply,he]
    simp only [e,smul_eq_mul,mul_one]
  rw [hAboveX,hPosX,hShift]

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.nativeH1_posPartAbove_eq_posPart_sub_constant
