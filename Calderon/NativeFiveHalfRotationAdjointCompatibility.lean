import Calderon.NativeFiveHalfCoefficientMultiplierTopology
import Calderon.NativeCoefficientRotationAdjointEndpointCompatibility
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeFiveHalfCoefficientMultiplier NativeThreeHalfCoefficientMultiplier

lemma sphereSobolevInclusionL_fivehalf_rotation_orders :
    sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num) =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by
  have hDelta : ((3/2:ℝ)-1)-((5/2:ℝ)-1) = (1/2:ℝ)-(3/2:ℝ) := by norm_num
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  have hLeft := sphereSobolevInclusionL_apply ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num) u k
  have hRight := sphereSobolevInclusionL_apply (3/2:ℝ) (1/2:ℝ) (by norm_num) u k
  exact hLeft.trans ((congrArg (fun r : ℝ => SpectralWeightedGraph.besselWeight r k • u k) hDelta).trans hRight.symm)

lemma nativeCoefficientRotationAdjoint_fivehalf_threehalf_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F4 : SmoothCoefficientJets 4) (F3 : SmoothCoefficientJets 3)
    (hCoeff : coefficientValue 4 F4 = coefficientValue 3 F3) (i j : Fin 3) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (nativeCoefficientRotationAdjointEndpointL (5/2:ℝ)
        (nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F4) i j) =
    (nativeCoefficientRotationAdjointEndpointL (3/2:ℝ)
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3) i j).comp
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  let Mh := nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F4
  let Ml := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3
  let Iin := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  apply ContinuousLinearMap.ext
  intro f
  have hM : Iin (Mh f) = Ml (Iin f) :=
    sphereSobolevInclusionL_nativeFiveHalfCoefficientMulL hcalc hF hO hD τ0 F4 F3 hCoeff f
  have hR : Iout (sphereSobolevRotationL (5/2:ℝ) i j (Mh f)) =
      sphereSobolevRotationL (3/2:ℝ) i j (Iin (Mh f)) := by
    have he := DFunLike.congr_fun
      (sphereSobolevRotationL_inclusion_comm (5/2:ℝ) (3/2:ℝ) (by norm_num) i j) (Mh f)
    have hPoint : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)
        (sphereSobolevRotationL (5/2:ℝ) i j (Mh f)) =
        sphereSobolevRotationL (3/2:ℝ) i j (Iin (Mh f)) := by
      simpa only [ContinuousLinearMap.comp_apply,Iin] using he
    have hNormalize := congrArg
      (fun I : SphereSobolev ((5/2:ℝ)-1) →L[ℝ] SphereSobolev ((3/2:ℝ)-1) =>
        I (sphereSobolevRotationL (5/2:ℝ) i j (Mh f)))
      sphereSobolevInclusionL_fivehalf_rotation_orders
    exact hNormalize.symm.trans hPoint
  change Iout (-(sphereSobolevRotationL (5/2:ℝ) i j (Mh f))) =
    -(sphereSobolevRotationL (3/2:ℝ) i j (Ml (Iin f)))
  rw [map_neg]
  exact congrArg (fun u : SphereSobolev (1/2:ℝ) => -u)
    (hR.trans (congrArg (sphereSobolevRotationL (3/2:ℝ) i j) hM))
end OAI.AnisotropicCalderon.SphereHarmonic
