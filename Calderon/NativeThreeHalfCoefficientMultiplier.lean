import Calderon.NativeH2ThreeHalfValueTrace
import Calderon.NativeCoefficientFluxTrace
import Calderon.NativeHarmonicHalfCoarseDualPairing

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeHarmonicLiftOrderCoherence NativeHarmonicHalfCoarseDualPairing MetricVolume

def nativeH2CoefficientSmoothData (F : SmoothCoefficientJets 3) : SmoothData :=
  ⟨coefficientValue 3 F,contDiff_coefficientValue 3 F⟩

lemma firstOrder_H2CoefficientMultiplier_eq_contDiffSMulL
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientJets 3) (U : BallSobolev 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(nativeH2CoefficientSmoothData F).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (nativeH2CoefficientSmoothData F).1 x‖ ≤ M) :
    TauCeti.Wkp.firstOrder 1 (coefficientMultiplier hcalc 2 F U) =
      TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
        (nativeH2CoefficientSmoothData F).1 (nativeH2CoefficientSmoothData F).2 hM hm hg
        (TauCeti.Wkp.firstOrder 1 U) := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder]
  apply Lp.ext
  have hmul := TauCeti.W1p.value_contDiffSMul_ae (nativeH2CoefficientSmoothData F).2 hM hm hg
    (TauCeti.Wkp.firstOrder 1 U)
  rw [TauCeti.Wkp.value_firstOrder] at hmul
  filter_upwards [coefficientMultiplier_value_ae hcalc 2 F U,hmul] with x hL hR
  rw [hL,hR]
  rfl

lemma valueTraceL_firstOrder_H2CoefficientMultiplier
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 3) (U : BallSobolev 2) :
    τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 (coefficientMultiplier hcalc 2 F U)) =
      sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F))
        (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)) := by
  obtain ⟨M,hM,hm,hg⟩ := exists_smooth_ball_multiplier_bound (nativeH2CoefficientSmoothData F)
  rw [firstOrder_H2CoefficientMultiplier_eq_contDiffSMulL hcalc F U hM hm hg]
  exact valueTraceL_contDiffSMulL τ0 (nativeH2CoefficientSmoothData F) hM hm hg _

lemma sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (U : BallSobolev 2) :
    sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
      (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 U) =
      sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_nativeThreeHalfValueTraceL,
    sphereSobolevCoefficientL_zeroEquiv]

lemma valueTraceL_harmonicH2LiftCompletion_coarse
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (f : SphereSobolev (3/2:ℝ)) :
    τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 (harmonicLiftCompletion hF f)) =
      (sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f) := by
  let Z := sphereSobolevZeroEquiv hO hD
  have hFirstL : TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 1 (harmonicLiftCompletion hF f) =
      TauCeti.Wkp.firstOrder 1 (harmonicLiftCompletion hF f) := rfl
  have hFirst := hFirstL.symm.trans (firstOrder_harmonicLiftCompletion hF hO f)
  have hTrace := congrArg (fun u : BallH1 => Z (τ0.valueTraceL u)) hFirst
  have hHalf := sphereSobolevZeroEquiv_valueTrace_harmonicFirstOrderLift hF hO hD τ0
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
  have hTrans := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T f)
    (sphereSobolevInclusionL_trans (3/2:ℝ) (1/2:ℝ) 0 (by norm_num) (by norm_num))
  apply Z.injective
  exact hTrace.trans (hHalf.trans (hTrans.trans
    (Z.apply_symm_apply (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f)).symm))

def nativeThreeHalfCoefficientMulL (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 3) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  (nativeThreeHalfValueTraceL hcalc hF hO hD τ0).comp
    ((coefficientMultiplier hcalc 2 F).comp (harmonicLiftCompletion hF))

lemma sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 3) (f : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F f) =
      sphereSobolevZeroEquiv hO hD
        (sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F))
          ((sphereSobolevZeroEquiv hO hD).symm (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) f))) := by
  let Z := sphereSobolevZeroEquiv hO hD
  let C := sphereContinuousScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData F))
  have hPoint : nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F f =
      nativeThreeHalfValueTraceL hcalc hF hO hD τ0
        (coefficientMultiplier hcalc 2 F (harmonicLiftCompletion hF f)) := rfl
  have hTrace := sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero hcalc hF hO hD τ0
    (coefficientMultiplier hcalc 2 F (harmonicLiftCompletion hF f))
  have hBulk := valueTraceL_firstOrder_H2CoefficientMultiplier hcalc τ0 F (harmonicLiftCompletion hF f)
  have hFree := valueTraceL_harmonicH2LiftCompletion_coarse hF hO hD τ0 f
  exact (congrArg (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)) hPoint).trans
    (hTrace.trans ((congrArg Z hBulk).trans
      (congrArg (fun u : SphereL2 => Z (C u)) hFree)))

lemma norm_nativeThreeHalfCoefficientMulL_le (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (F : SmoothCoefficientJets 3) :
    ‖nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F‖ ≤
      ‖nativeThreeHalfValueTraceL hcalc hF hO hD τ0‖ *
        ((sobolevMultiplierBound hcalc 2*‖F‖)*‖harmonicLiftCompletion hF‖) := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_coefficientMultiplier_le hcalc 2 F) (norm_nonneg _))

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeH2CoefficientSmoothData

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.firstOrder_H2CoefficientMultiplier_eq_contDiffSMulL

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.valueTraceL_firstOrder_H2CoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.valueTraceL_harmonicH2LiftCompletion_coarse

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.norm_nativeThreeHalfCoefficientMulL_le
