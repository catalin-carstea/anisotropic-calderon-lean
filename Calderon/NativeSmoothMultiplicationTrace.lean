import Calderon.NativeGlobalSmoothH1Density
import Calderon.SphereContinuousScalarMultiplier
import TauCeti.Analysis.Sobolev.W1p.Multiplication

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic

theorem exists_smooth_ball_multiplier_bound (m : SmoothData) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M) ∧
      (∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M) := by
  have hm : Continuous (fun x : R3 => ‖m.1 x‖) := m.2.continuous.norm
  have hg : Continuous (fun x : R3 => ‖gradient m.1 x‖) :=
    (m.2.gradient_right (m := 0) (by simp)).continuous.norm
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0 : R3) 1).bddAbove_image hm.continuousOn
  obtain ⟨G,hG⟩ := (isCompact_closedBall (0 : R3) 1).bddAbove_image hg.continuousOn
  refine ⟨max 0 (max A G),le_max_left _ _,?_,?_⟩
  · intro x hx
    have hb : ‖m.1 x‖ ≤ A := hA ⟨x,Metric.ball_subset_closedBall hx,rfl⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans ((le_max_left A G).trans (le_max_right 0 (max A G)))
  · intro x hx
    have hb : ‖gradient m.1 x‖ ≤ G := hG ⟨x,Metric.ball_subset_closedBall hx,rfl⟩
    exact hb.trans ((le_max_right A G).trans (le_max_right 0 (max A G)))

theorem contDiffSMulL_smoothSobolev
    (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (f : SmoothData) :
    TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) m.1 m.2 hM hm hg (smoothSobolev f) =
        smoothSobolev ⟨m.1*f.1,m.2.mul f.2⟩ := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae m.2 hM hm hg (smoothSobolev f),
    value_smoothSobolev_ae f,value_smoothSobolev_ae ⟨m.1*f.1,m.2.mul f.2⟩]
    with x hmul hf hprod
  rw [hmul,hf,hprod]
  rfl

theorem valueTraceL_contDiffSMulL
    (τ0 : UnitBallValueTrace) (m : SmoothData) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M)
    (u : BallH1) :
    τ0.valueTraceL (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) m.1 m.2 hM hm hg u) =
        sphereContinuousScalarMulL (smoothSphereValue m) (τ0.valueTraceL u) := by
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg
  let A : BallH1 →L[ℝ] SphereL2 := τ0.valueTraceL.comp S
  let C : BallH1 →L[ℝ] SphereL2 :=
    (sphereContinuousScalarMulL (smoothSphereValue m)).comp τ0.valueTraceL
  have hEq : (A : BallH1 → SphereL2) = C := by
    apply denseRange_smoothSobolev.equalizer A.continuous C.continuous
    funext f
    change τ0.valueTraceL (S (smoothSobolev f)) =
      sphereContinuousScalarMulL (smoothSphereValue m) (τ0.valueTraceL (smoothSobolev f))
    change τ0.valueTraceL (TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg (smoothSobolev f)) = _
    rw [contDiffSMulL_smoothSobolev,τ0.valueTrace_smooth,τ0.valueTrace_smooth,
      sphereContinuousScalarMulL_toLp]
    congr 1
  exact congr_fun hEq u

end OAI.AnisotropicCalderon.DirichletFamily
