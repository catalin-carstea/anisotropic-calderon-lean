import Calderon.NativeThreeHalfCoefficientMultiplier
import Calderon.NativeSmoothBallSobolev

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-COORDINATE-UNIT-PRODUCT-EXPANSION-v001.md. Concrete existing bump, actual high multiplier identity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic

def unitSphereCoefficientJets (k : ℕ) : SmoothCoefficientJets k :=
  compactCoefficient k (unitBallSmoothCutoff : R3 → ℝ)
    unitBallSmoothCutoff.contDiff unitBallSmoothCutoff.hasCompactSupport

lemma coefficientValue_unitSphereCoefficientJets (k : ℕ) (x : UnitSphere) :
    coefficientValue k (unitSphereCoefficientJets k) x.val = 1 := by
  have hValue := congrFun (coefficientValue_compactCoefficient k
    (unitBallSmoothCutoff : R3 → ℝ) unitBallSmoothCutoff.contDiff unitBallSmoothCutoff.hasCompactSupport) x.val
  apply hValue.trans
  apply unitBallSmoothCutoff.one_of_mem_closedBall
  change dist x.val (0 : R3) ≤ (2 : ℝ)
  have hx : dist x.val (0 : R3) = 1 := Metric.mem_sphere.mp x.property
  linarith

attribute [local irreducible] nativeThreeHalfCoefficientMulL sphereSobolevInclusionL sphereSobolevZeroEquiv

lemma nativeThreeHalfCoefficientMulL_eq_id_of_sphere_eq_one
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 3) (hSphere : ∀ x : UnitSphere, coefficientValue 3 F x.val = 1) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      ContinuousLinearMap.id ℝ (SphereSobolev (3/2 : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply sphereSobolevInclusionL_injective (3/2 : ℝ) 0 (by norm_num)
  let Z := sphereSobolevZeroEquiv hO hD
  let I := sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let c := smoothSphereValue (nativeH2CoefficientSmoothData F)
  have hScalar (v : SphereL2) : sphereContinuousScalarMulL c v = v := by
    apply Lp.ext
    filter_upwards [sphereContinuousScalarMul_value_ae c v] with x hx
    exact hx.trans (by
      change coefficientValue 3 F x.val * v x = v x
      rw [hSphere x,one_mul])
  exact (sphereSobolevInclusionL_nativeThreeHalfCoefficientMulL_zero hcalc hF hO hD τ0 F f).trans
    ((congrArg Z (hScalar (Z.symm (I f)))).trans (Z.apply_symm_apply (I f)))

lemma nativeThreeHalfCoefficientMulL_unitSphereCoefficientJets
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (unitSphereCoefficientJets 3) =
      ContinuousLinearMap.id ℝ (SphereSobolev (3/2 : ℝ)) :=
  nativeThreeHalfCoefficientMulL_eq_id_of_sphere_eq_one hcalc hF hO hD τ0
    (unitSphereCoefficientJets 3) (coefficientValue_unitSphereCoefficientJets 3)

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.unitSphereCoefficientJets
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.coefficientValue_unitSphereCoefficientJets
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL_eq_id_of_sphere_eq_one
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL_unitSphereCoefficientJets
