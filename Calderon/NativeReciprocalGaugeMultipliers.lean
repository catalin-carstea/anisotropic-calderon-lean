import Calderon.ActualReferenceGaugePrincipalFamily
import Calderon.NativeCoefficientH1ProductDerivative
import Calderon.ActualReferenceNormalHalfInverseDualAdjunction
import Calderon.NativeSmoothOperatorRealization
import Calderon.ActualReferenceWeakEnergyApply
import Calderon.BilinearRotationInvertibility
import Calderon.NativeContinuousCoefficientOrthogonalEnergy
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceStrongEnergy
import Calderon.DirichletForcingInjectivity
import Calderon.ActualReferenceWeakDirichletEvaluationReference

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator MetricVolume
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
theorem nativeCoefficientH1ProductL_mem_zero
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2) (u : BallH1Zero) :
    nativeCoefficientH1ProductL hcalc F (u : BallH1) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  rw [nativeCoefficientH1ProductL_eq_contDiffSMulL hcalc F hM hm hg,
    TauCeti.W1p.contDiffSMulL_apply]
  exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule
    (coefficientSmoothData F).2 hM hm hg u.property

def nativeCoefficientZeroProductL
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2) :
    BallH1Zero →L[ℝ] BallH1Zero :=
  { toFun := fun u => ⟨nativeCoefficientH1ProductL hcalc F (u : BallH1),
      nativeCoefficientH1ProductL_mem_zero hcalc F u⟩
    map_add' := by
      intro u v
      apply Subtype.ext
      exact (nativeCoefficientH1ProductL hcalc F).map_add (u : BallH1) (v : BallH1)
    map_smul' := by
      intro c u
      apply Subtype.ext
      exact (nativeCoefficientH1ProductL hcalc F).map_smul c (u : BallH1)
    cont := ((nativeCoefficientH1ProductL hcalc F).continuous.comp
      continuous_subtype_val).subtype_mk _ }

theorem nativeCoefficientZeroProductL_coe
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2) (u : BallH1Zero) :
    (nativeCoefficientZeroProductL hcalc F u : BallH1) =
      nativeCoefficientH1ProductL hcalc F (u : BallH1) := rfl

theorem nativeCoefficientZeroProductL_comp_eq_id
    (hcalc : FixedSobolevCalculus) (F G : SmoothCoefficientJets 2)
    (hFG : ∀ x ∈ (ballOpens : Set R3),
      coefficientValue 2 F x * coefficientValue 2 G x = 1) :
    (nativeCoefficientZeroProductL hcalc F).comp (nativeCoefficientZeroProductL hcalc G) =
      ContinuousLinearMap.id ℝ BallH1Zero := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [nativeCoefficientH1ProductL_value_ae hcalc F
      (nativeCoefficientH1ProductL hcalc G (u : BallH1)),
    nativeCoefficientH1ProductL_value_ae hcalc G (u : BallH1),
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hF hG hx
  change TauCeti.W1p.value
    (nativeCoefficientH1ProductL hcalc F
      (nativeCoefficientH1ProductL hcalc G (u : BallH1))) x = TauCeti.W1p.value (u : BallH1) x
  rw [hF,hG,← mul_assoc,hFG x hx,one_mul]

theorem nativeCoefficientZeroProductL_isInvertible_of_reciprocal
    (hcalc : FixedSobolevCalculus) (F G : SmoothCoefficientJets 2)
    (hFG : ∀ x ∈ (ballOpens : Set R3),
      coefficientValue 2 F x * coefficientValue 2 G x = 1) :
    (nativeCoefficientZeroProductL hcalc F).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (nativeCoefficientZeroProductL_comp_eq_id hcalc F G hFG)
  apply nativeCoefficientZeroProductL_comp_eq_id
  intro x hx
  rw [mul_comm]
  exact hFG x hx

theorem coefficientMultiplier_comp_eq_id_of_reciprocal
    (hcalc : FixedSobolevCalculus) (k : ℕ) (F G : SmoothCoefficientJets (k+1))
    (hFG : ∀ x ∈ (ballOpens : Set R3),
      coefficientValue (k+1) F x * coefficientValue (k+1) G x = 1) :
    (coefficientMultiplier hcalc k F).comp (coefficientMultiplier hcalc k G) =
      ContinuousLinearMap.id ℝ (BallSobolev k) := by
  apply ContinuousLinearMap.ext
  intro u
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F (coefficientMultiplier hcalc k G u),
    coefficientMultiplier_value_ae hcalc k G u,
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hF hG hx
  change TauCeti.Wkp.value k (coefficientMultiplier hcalc k F (coefficientMultiplier hcalc k G u)) x =
    TauCeti.Wkp.value k u x
  rw [hF,hG,← mul_assoc,hFG x hx,one_mul]

theorem coefficientMultiplier_isInvertible_of_reciprocal
    (hcalc : FixedSobolevCalculus) (k : ℕ) (F G : SmoothCoefficientJets (k+1))
    (hFG : ∀ x ∈ (ballOpens : Set R3),
      coefficientValue (k+1) F x * coefficientValue (k+1) G x = 1) :
    (coefficientMultiplier hcalc k F).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (coefficientMultiplier_comp_eq_id_of_reciprocal hcalc k F G hFG)
  apply coefficientMultiplier_comp_eq_id_of_reciprocal
  intro x hx
  rw [mul_comm]
  exact hFG x hx


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
