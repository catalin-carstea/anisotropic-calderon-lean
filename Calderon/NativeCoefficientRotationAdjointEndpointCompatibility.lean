import Calderon.SphereSobolevRotationInclusionOrders
import Calderon.NativeOrderOneCoefficientMultiplierTopology
import Calderon.NativeOrderOneScalarRotationAdjunction
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier

lemma sphereSobolevRotationL_inclusion_comm (s t : ℝ) (hts : t ≤ s) (i j : Fin 3) :
    (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (sphereSobolevRotationL s i j) =
      (sphereSobolevRotationL t i j).comp (sphereSobolevInclusionL s t hts) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext (t-1)
  intro k
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_rotation]

def nativeCoefficientRotationAdjointEndpointL (s : ℝ)
    (M : SphereSobolev s →L[ℝ] SphereSobolev s) (i j : Fin 3) :
    SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  -(sphereSobolevRotationL s i j).comp M

lemma nativeCoefficientRotationAdjoint_high_half_compatibility
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F3 : SmoothCoefficientJets 3) (F2 : SmoothCoefficientJets 2)
    (hCoeff : coefficientValue 3 F3 = coefficientValue 2 F2) (i j : Fin 3) :
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
      (nativeCoefficientRotationAdjointEndpointL (3/2:ℝ)
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3) i j) =
    (nativeCoefficientRotationAdjointEndpointL (1/2:ℝ)
      (nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2) i j).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let Mh := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F3
  let Ml := nativeHalfCoefficientMulL hcalc hF hO hD τ0 F2
  let Iin := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)
  apply ContinuousLinearMap.ext
  intro f
  have hM : Iin (Mh f) = Ml (Iin f) :=
    congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 F3 F2 hCoeff)
  have hR : Iout (sphereSobolevRotationL (3/2:ℝ) i j (Mh f)) =
      sphereSobolevRotationL (1/2:ℝ) i j (Iin (Mh f)) := by
    have he := congrArg
      (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev ((1/2:ℝ)-1) => T (Mh f))
      (sphereSobolevRotationL_inclusion_comm (3/2:ℝ) (1/2:ℝ) (by norm_num) i j)
    have hPoint : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1/2:ℝ)-1) (by norm_num)
        (sphereSobolevRotationL (3/2:ℝ) i j (Mh f)) =
        sphereSobolevRotationL (1/2:ℝ) i j (Iin (Mh f)) := by
      simpa only [ContinuousLinearMap.comp_apply,Iin] using he
    have hNormalize := congrArg
      (fun I : SphereSobolev ((3/2:ℝ)-1) →L[ℝ] SphereSobolev ((1/2:ℝ)-1) =>
        I (sphereSobolevRotationL (3/2:ℝ) i j (Mh f)))
      sphereSobolevInclusionL_threehalf_rotation_orders
    exact hNormalize.symm.trans hPoint
  change Iout (-(sphereSobolevRotationL (3/2:ℝ) i j (Mh f))) =
    -(sphereSobolevRotationL (1/2:ℝ) i j (Ml (Iin f)))
  rw [map_neg]
  exact congrArg (fun u : SphereSobolev (-1/2:ℝ) => -u)
    (hR.trans (congrArg (sphereSobolevRotationL (1/2:ℝ) i j) hM))

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevRotationL_inclusion_comm
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeCoefficientRotationAdjointEndpointL
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.nativeCoefficientRotationAdjoint_high_half_compatibility
