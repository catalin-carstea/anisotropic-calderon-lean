import Calderon.RadiusTwoNativeDilationJets

/-! Full EXPANSION.json precedes this literal native-to-physical representative transport. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem quasiMeasurePreserving_radiusTwo_comp_half :
    QuasiMeasurePreserving (fun z : R3 => (1/2 : ℝ) • z)
      ((volume : Measure R3).restrict radiusTwoOpens)
      ((volume : Measure R3).restrict ballOpens) := by
  apply (quasiMeasurePreserving_smul (μ := (volume : Measure R3))
    (by norm_num : (1/2 : ℝ) ≠ 0)).restrict
  intro z hz
  change z ∈ Metric.ball (0 : R3) 2 at hz
  have hn : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
  change (1/2 : ℝ) • z ∈ ball (0 : R3) 1
  rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
  norm_num
  linarith

theorem radiusTwo_continuousRepresentative_transport
    (w : RadiusTwoH1Zero) (U : BallSobolev 2)
    (hU : TauCeti.Wkp.firstOrder 1 U = (radiusTwoNativeZeroDilation w : BallH1))
    (a : ℝ) (F : R3 → ℝ) (hF : Continuous F)
    (hFA : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a → F y = TauCeti.Wkp.value 2 U y) :
    Continuous (fun z : R3 => F ((1/2 : ℝ) • z)) ∧
      ∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
        (1/2 : ℝ) • z ∈ closedBall (0 : R3) a →
          F ((1/2 : ℝ) • z) = TauCeti.W1p.value (w : RadiusTwoH1) z := by
  have hVal : TauCeti.Wkp.value 2 U =
      radiusTwoNativeL2Dilation (TauCeti.W1p.value (w : RadiusTwoH1)) := by
    have h := congrArg TauCeti.W1p.value hU
    rw [TauCeti.Wkp.value_firstOrder,value_radiusTwoNativeZeroDilation] at h
    exact h
  have hAE : ∀ᵐ y ∂(volume : Measure R3).restrict ballOpens,
      y ∈ closedBall (0 : R3) a →
        F y = TauCeti.W1p.value (w : RadiusTwoH1) ((2 : ℝ) • y) := by
    rw [hVal] at hFA
    filter_upwards [hFA,radiusTwoNativeL2Dilation_apply_ae
      (TauCeti.W1p.value (w : RadiusTwoH1))] with y hFy hDy hy
    exact (hFy hy).trans hDy
  have hHalf : Continuous (fun z : R3 => (1/2 : ℝ) • z) :=
    continuous_const_smul (1/2 : ℝ)
  refine ⟨hF.comp hHalf,?_⟩
  filter_upwards [quasiMeasurePreserving_radiusTwo_comp_half.ae hAE] with z hz hza
  have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by
    rw [smul_smul]
    norm_num
  exact (hz hza).trans (congrArg (fun x : R3 => TauCeti.W1p.value (w : RadiusTwoH1) x) hCancel)

end OAI.AnisotropicCalderon.ExteriorSource
