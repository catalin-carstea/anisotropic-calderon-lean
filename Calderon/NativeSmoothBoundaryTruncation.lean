import Calderon.SmoothSobolevBridge
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.Sobolev.W1p.LevelSet

/-! EXPANSION.json precedes constructive compact truncation membership.
This does not assume SmoothBoundaryZeroClosure or an arbitrary trace-kernel converse. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.EnergyBridge

theorem smoothSobolev_positive_boundary_truncation_mem_zero
    (f : SmoothData) (hSphere : ∀ x : R3, ‖x‖ = 1 → f.1 x = 0)
    (ε : ℝ) (hε : 0 < ε) :
    TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (smoothSobolev f - ε • smoothSobolev ⟨fun _ : R3 => (1 : ℝ), contDiff_const⟩) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let e : SmoothData := ⟨fun _ : R3 => (1 : ℝ), contDiff_const⟩
  let u : BallH1 := smoothSobolev f - ε • smoothSobolev e
  let K : Set R3 := closedBall (0 : R3) 1 ∩ {x | ε ≤ f.1 x}
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : R3) 1).inter_right
      (isClosed_le continuous_const f.2.continuous)
  have hKSub : K ⊆ (ballOpens : Set R3) := by
    intro x hx
    have hn : ‖x‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hx.1
    have hne : ‖x‖ ≠ 1 := by
      intro heq
      have hfx := hSphere x heq
      have heps : ε ≤ 0 := hfx ▸ hx.2
      exact (not_le_of_gt hε) heps
    change x ∈ ball (0 : R3) 1
    simpa only [mem_ball, dist_zero_right] using lt_of_le_of_ne hn hne
  have hValueSplit : TauCeti.W1p.value u =
      TauCeti.W1p.value (smoothSobolev f) - ε • TauCeti.W1p.value (smoothSobolev e) := by
    dsimp only [u]
    simp only [← TauCeti.W1p.valueL_apply, map_sub, map_smul]
  have hValue : TauCeti.W1p.value u =ᵐ[((volume : Measure R3).restrict ballOpens)]
      (fun x => f.1 x - ε) := by
    rw [hValueSplit]
    filter_upwards [Lp.coeFn_sub (TauCeti.W1p.value (smoothSobolev f))
        (ε • TauCeti.W1p.value (smoothSobolev e)),
      Lp.coeFn_smul ε (TauCeti.W1p.value (smoothSobolev e)),
      value_smoothSobolev_ae f,value_smoothSobolev_ae e] with x hSub hSmul hf he
    rw [hSub,Pi.sub_apply,hSmul,Pi.smul_apply,hf,he]
    simp only [e,smul_eq_mul,mul_one]
  have hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hPos : TauCeti.W1p.value (TauCeti.W1p.posPart hp u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      (fun x => max (TauCeti.W1p.value u x) 0) := by
    rw [TauCeti.W1p.value_posPart]
    exact Lp.coeFn_posPart (TauCeti.W1p.value u)
  apply TauCeti.W1p.mem_w1p0Submodule_of_isCompact hp hK hKSub
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet,hValue,hPos] with x hx hValueX hPosX
  intro hxK
  have hlt : f.1 x < ε := lt_of_not_ge (fun hge => hxK ⟨ball_subset_closedBall hx,hge⟩)
  rw [hPosX,hValueX]
  exact max_eq_right (sub_nonpos.mpr hlt.le)

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.smoothSobolev_positive_boundary_truncation_mem_zero
