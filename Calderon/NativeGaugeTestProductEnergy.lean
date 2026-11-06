import Calderon.NativeReciprocalGaugeMultipliers
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
theorem nativeCoefficientH1ProductL_gradient_ae
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2) (v : BallH1) :
    TauCeti.W1p.gradient (nativeCoefficientH1ProductL hcalc F v)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => coefficientValue 2 F x • TauCeti.W1p.gradient v x +
        TauCeti.W1p.value v x • gradient (coefficientValue 2 F) x := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (coefficientSmoothData F)
  rw [nativeCoefficientH1ProductL_eq_contDiffSMulL hcalc F hM hm hg,
    TauCeti.W1p.contDiffSMulL_apply]
  exact TauCeti.W1p.gradient_contDiffSMul_ae
    (coefficientSmoothData F).2 hM hm hg v

theorem energyFormH1_nativeCoefficient_test_product
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 2)
    (A a : MatrixField) (b : R3 → R3)
    (hScale : ∀ x ∈ (ballOpens : Set R3), coefficientValue 2 F x • A x = a x)
    (hDrift : ∀ x ∈ (ballOpens : Set R3), ∀ v : R3,
      TauCeti.PDE.matrixBilinearForm (A x) (gradient (coefficientValue 2 F) x) v =
        inner ℝ (b x) v)
    (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      A 0 0 u (nativeCoefficientH1ProductL hcalc F v) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a b 0 u v := by
  rw [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [nativeCoefficientH1ProductL_gradient_ae hcalc F v,
    nativeCoefficientH1ProductL_value_ae hcalc F v,
    ae_restrict_mem ballOpens.isOpen.measurableSet] with x hGrad hValue hx
  simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.jetField_apply,
    TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,Pi.zero_apply,
    inner_zero_left,zero_mul,add_zero]
  rw [hGrad,map_add,map_smul,map_smul]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hS := hScale x hx
  have hD := hDrift x hx (TauCeti.W1p.gradient u x)
  rw [hD]
  have hB : coefficientValue 2 F x *
      TauCeti.PDE.matrixBilinearForm (A x) (TauCeti.W1p.gradient v x)
        (TauCeti.W1p.gradient u x) =
      TauCeti.PDE.matrixBilinearForm (a x) (TauCeti.W1p.gradient v x)
        (TauCeti.W1p.gradient u x) := by
    rw [← hS]
    simp only [TauCeti.PDE.matrixBilinearForm_apply,Matrix.smul_mulVec,
      dotProduct_smul,smul_eq_mul]
  rw [hB]
  ring

theorem bilinearForm_isInvertible_of_isCoercive
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (E : V →L[ℝ] StrongDual ℝ V) (hE : IsCoercive E) : E.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := functionalInverse E)
  · apply ContinuousLinearMap.ext
    intro ell
    apply ContinuousLinearMap.ext
    intro v
    exact apply_functionalInverse E hE ell v
  · apply ContinuousLinearMap.ext
    intro u
    exact (eq_functionalInverse E hE (E u) u (fun _ => rfl)).symm


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
