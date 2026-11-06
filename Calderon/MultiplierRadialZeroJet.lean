import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge CommonSupportSlices BoundedParameterSmoothness

instance instFiniteMeasureUnitBall : IsFiniteMeasure ((volume : Measure R3).restrict ballOpens) :=
  ⟨by simpa only [Measure.restrict_apply_univ,coe_ballOpens] using
    ((measure_mono (show B ⊆ Metric.closedBall (0 : R3) 1 from Metric.ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : R3) 1).measure_lt_top)⟩

def unitBallBoundedToLpL : (R3 →ᵇ ℝ) →L[ℝ]
    Lp ℝ ⊤ ((volume : Measure R3).restrict ballOpens) :=
  BoundedContinuousFunction.toLp ⊤ ((volume : Measure R3).restrict ballOpens) ℝ

theorem unitBallBoundedToLpL_ae (f : R3 →ᵇ ℝ) :
    unitBallBoundedToLpL f =ᵐ[((volume : Measure R3).restrict ballOpens)] f :=
  BoundedContinuousFunction.coeFn_toLp ⊤ ((volume : Measure R3).restrict ballOpens) ℝ f

theorem coefficientMultiplier_commonSupport_value_eq (hcalc : FixedSobolevCalculus) (k : ℕ)
    (g : ℝ × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ r z, z ∉ K → g (r,z) = 0) (r : ℝ) (u : BallSobolev k) :
    TauCeti.Wkp.value k (coefficientMultiplier hcalc k
      (commonSupportCoefficientFamily (k+1) g hg K hK hz r) u) =
      unitBallWeightedLpL (unitBallBoundedToLpL (commonSupportSlice g hg.continuous K hK hz r))
        (TauCeti.Wkp.value k u) := by
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k
    (commonSupportCoefficientFamily (k+1) g hg K hK hz r) u,
    unitBallWeightedLpL_ae (unitBallBoundedToLpL (commonSupportSlice g hg.continuous K hK hz r))
      (TauCeti.Wkp.value k u),
    unitBallBoundedToLpL_ae (commonSupportSlice g hg.continuous K hK hz r)] with z hmul hprod hb
  rw [hmul,hprod,hb,coefficientValue_commonSupportCoefficientFamily]
  rfl

theorem hasDerivAt_commonSupportLp_zero
    (g : ℝ × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ r z, z ∉ K → g (r,z) = 0)
    (hzero : ∀ z ∈ (ballOpens : Set R3), HasDerivAt (fun r : ℝ => g (r,z)) 0 0) :
    HasDerivAt (fun r => unitBallBoundedToLpL (commonSupportSlice g hg.continuous K hK hz r)) 0 0 := by
  let F := commonSupportSlice g hg.continuous K hK hz
  have hf : HasDerivAt F (deriv F 0) 0 :=
    ((contDiff_infty_commonSupportSlice g hg K hK hz).differentiable (by simp) 0).hasDerivAt
  have hd : ∀ z ∈ (ballOpens : Set R3), deriv F 0 z = 0 := by
    intro z hzball
    have hzder := (BoundedContinuousFunction.evalCLM (α := R3) (β := ℝ) ℝ z).hasFDerivAt.comp_hasDerivAt 0 hf
    change HasDerivAt (fun r : ℝ => g (r,z)) (deriv F 0 z) 0 at hzder
    exact hzder.unique (hzero z hzball)
  have he : unitBallBoundedToLpL (deriv F 0) = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_zero ℝ ⊤ ((volume : Measure R3).restrict ballOpens),
      unitBallBoundedToLpL_ae (deriv F 0),
      ae_restrict_mem (show MeasurableSet (ballOpens : Set R3) from ballOpens.isOpen.measurableSet)]
      with z h0 hz hzball
    rw [hz,hd z hzball,h0]
    rfl
  simpa only [he,Function.comp_def,F] using unitBallBoundedToLpL.hasFDerivAt.comp_hasDerivAt 0 hf

theorem hasDerivAt_commonSupport_coefficientMultiplier_zero
    (hcalc : FixedSobolevCalculus) (k : ℕ)
    (g : ℝ × R3 → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ r z, z ∉ K → g (r,z) = 0)
    (hzero : ∀ z ∈ (ballOpens : Set R3), HasDerivAt (fun r : ℝ => g (r,z)) 0 0) :
    HasDerivAt (fun r => coefficientMultiplier hcalc k
      (commonSupportCoefficientFamily (k+1) g hg K hK hz r)) 0 0 := by
  let M := fun r => coefficientMultiplier hcalc k
    (commonSupportCoefficientFamily (k+1) g hg K hK hz r)
  have hm : HasDerivAt M (deriv M 0) 0 :=
    ((contDiff_commonSupport_actual_coefficientMultiplier hcalc k g hg K hK hz).differentiable
      (by simp) 0).hasDerivAt
  have he : deriv M 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply TauCeti.Wkp.ext k
    have hv := (TauCeti.Wkp.valueL (mu := (volume : Measure R3)) (Omega := ballOpens)
      (p := 2) k).hasFDerivAt.comp_hasDerivAt 0
        (hm.clm_apply (hasDerivAt_const (0 : ℝ) u))
    have hp := (unitBallWeightedLpL.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_commonSupportLp_zero g hg K hK hz hzero)).clm_apply
        (hasDerivAt_const (0 : ℝ) (TauCeti.Wkp.value k u))
    have hfun : (fun r => TauCeti.Wkp.valueL k (M r u)) =
        fun r => unitBallWeightedLpL
          (unitBallBoundedToLpL (commonSupportSlice g hg.continuous K hK hz r))
          (TauCeti.Wkp.value k u) := by
      funext r
      exact coefficientMultiplier_commonSupport_value_eq hcalc k g hg K hK hz r u
    simp only [Function.comp_def,map_zero,add_zero] at hv hp
    rw [hfun] at hv
    have hx := hv.unique hp
    change TauCeti.Wkp.valueL k ((deriv M 0) u) = TauCeti.Wkp.valueL k (0 : BallSobolev k)
    simpa only [map_zero,ContinuousLinearMap.zero_apply] using hx
  simpa only [he] using hm
end OAI.AnisotropicCalderon.DirichletFamily
