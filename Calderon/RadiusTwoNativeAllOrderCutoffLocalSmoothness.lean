import Calderon.RadiusTwoNativeAllOrderSmoothValue
import Mathlib.MeasureTheory.Measure.OpenPos

/-! EXPANSION-local-identification.json precedes identification of the SAME selected value. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma exists_contDiffOn_neighborhood_of_radiusTwoNativeAllOrder_cutoff
    (hcalc : FixedSobolevCalculus) (K : RadiusTwoL2)
    (w : RadiusTwoH1Zero) (η : R3 → ℝ)
    (hValue : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z => η z * K z))
    (hLift : ∀ s : ℕ, ∃ U : BallSobolev (s+2),
      TauCeti.Wkp.firstOrder (s+1) U = (radiusTwoNativeZeroDilation w : BallH1))
    (G : R3 → ℝ) (O : Set R3) (hO : IsOpen O)
    (hG : ContinuousOn G O) (hGAE : G =ᵐ[(volume : Measure R3).restrict O] (K : R3 → ℝ))
    (x : R3) (hxN : x ∈ radiusTwoOpens) (hxO : x ∈ O)
    (ε : ℝ) (hε : 0 < ε) (hOne : ∀ z ∈ ball x ε, η z = 1) :
    ∃ V : Set R3, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ ContDiffOn ℝ ∞ G V := by
  trace "PROOF ENTER SAME selected native cutoff local smoothness"
  have hxNorm : ‖x‖ < 2 := by
    change x ∈ ball (0 : R3) 2 at hxN
    exact mem_ball_zero_iff.mp hxN
  let a : ℝ := (‖x‖/2+1)/2
  have ha : 0 < a := by dsimp only [a]; nlinarith [norm_nonneg x]
  have ha1 : a < 1 := by dsimp only [a]; linarith
  have hxBall : x ∈ ball (0 : R3) (2*a) := by
    apply mem_ball_zero_iff.mpr
    dsimp only [a]
    linarith
  let P : (R3 → ℝ) → Prop := fun F =>
    Continuous F ∧ ContDiffOn ℝ ∞ F (ball (0 : R3) (2*a)) ∧
    (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] F
  have hData : ∃ F : R3 → ℝ, P F :=
    exists_radiusTwoNativeAllOrder_innerBall_smooth_value hcalc w hLift a ha ha1
  trace "SMOOTH PHYSICAL PACKAGE MADE SAME selected local smoothness"
  refine Exists.elim hData ?_
  intro F hF
  let V : Set R3 := (ball x ε ∩ ball (0 : R3) (2*a)) ∩ O
  have hVOpen : IsOpen V := (isOpen_ball.inter isOpen_ball).inter hO
  have hxV : x ∈ V := ⟨⟨mem_ball_self hε,hxBall⟩,hxO⟩
  have hVO : V ⊆ O := fun z hz => hz.2
  have hVB : V ⊆ ball (0 : R3) (2*a) := fun z hz => hz.1.2
  have hVN : V ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    change z ∈ ball (0 : R3) 2
    exact ball_subset_ball (by linarith : 2*a ≤ 2) (hVB hz)
  have hMuN : (volume : Measure R3).restrict V ≤
      (volume : Measure R3).restrict radiusTwoOpens := Measure.restrict_mono_set volume hVN
  have hMuB : (volume : Measure R3).restrict V ≤
      (volume : Measure R3).restrict (ball (0 : R3) (2*a)) := Measure.restrict_mono_set volume hVB
  have hMuO : (volume : Measure R3).restrict V ≤
      (volume : Measure R3).restrict O := Measure.restrict_mono_set volume hVO
  have hEqualAE : F =ᵐ[(volume : Measure R3).restrict V] G := by
    filter_upwards [hValue.filter_mono (ae_mono hMuN),hF.2.2.filter_mono (ae_mono hMuB),
      hGAE.filter_mono (ae_mono hMuO),ae_restrict_mem hVOpen.measurableSet]
        with z hVal hFVal hGVal hzV
    have hEta : η z = 1 := hOne z hzV.1.1
    exact hFVal.symm.trans ((hVal.trans (by rw [hEta,one_mul])).trans hGVal.symm)
  trace "ACTUAL AE IDENTIFICATION MADE SAME selected local smoothness"
  have hEq : EqOn F G V := Measure.eqOn_open_of_ae_eq hEqualAE hVOpen
    hF.1.continuousOn (hG.mono hVO)
  have hSmooth : ContDiffOn ℝ ∞ G V :=
    (hF.2.1.mono hVB).congr (fun z hz => (hEq hz).symm)
  exact ⟨V,hVOpen,hxV,hVO,hSmooth⟩

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_contDiffOn_neighborhood_of_radiusTwoNativeAllOrder_cutoff
