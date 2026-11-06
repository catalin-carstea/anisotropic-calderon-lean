import Calderon.NativeH2ThreeHalfValueTrace
import Calderon.SphereSobolevPairingInclusion

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace

attribute [local irreducible] nativeThreeHalfValueTraceL sphereSobolevInclusionL sphereSobolevZeroEquiv

theorem sphereSobolevInclusionL_zero_nativeThreeHalfTrace_smooth
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (v : SmoothData) :
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 v)) =
      sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (smoothSobolev v)) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_nativeThreeHalfValueTraceL,
    sphereSobolevCoefficientL_zeroEquiv,firstOrder_smoothBallSobolev]

theorem nativeThreeHalfTrace_dualPairing_eq_L2_valueTrace
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (Psi : SphereSobolev (3/2 : ℝ)) (v : SmoothData) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) Psi))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 v))) =
      ⟪(sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Psi),
        τ0.valueTraceL (smoothSobolev v)⟫_ℝ := by
  have hCompose (z : SphereSobolev (3/2 : ℝ)) :
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) z) =
      sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) z := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 => T z)
        (sphereSobolevInclusionL_trans (3/2 : ℝ) (1/2 : ℝ) 0 (by norm_num) (by norm_num))
  let T : SphereSobolev (3/2 : ℝ) := nativeThreeHalfValueTraceL hcalc hF hO hD τ0 (smoothBallSobolev 2 v)
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  have hPair := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) (I Psi) (I T)
  have hBoth := congrArg₂ (fun x y : SphereSobolev 0 => inner ℝ x y) (hCompose Psi) (hCompose T)
  have hTrace := congrArg (fun x : SphereSobolev 0 =>
      inner ℝ (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Psi) x)
    (sphereSobolevInclusionL_zero_nativeThreeHalfTrace_smooth hcalc hF hO hD τ0 v)
  have h := ((sphereSobolevZeroEquiv hO hD).symm.inner_map_map
    (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) Psi)
    (sphereSobolevZeroEquiv hO hD (τ0.valueTraceL (smoothSobolev v)))).symm
  have hIso := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h
  exact hPair.trans (hBoth.trans (hTrace.trans hIso))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
