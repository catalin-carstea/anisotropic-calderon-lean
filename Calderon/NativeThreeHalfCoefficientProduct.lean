import Calderon.NativeThreeHalfProductTrace

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-COEFFICIENT-PRODUCT-ALGEBRA-EXPANSION-v001.md. Literal scalar product before native and boundary maps. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge DriftBootstrap

attribute [local irreducible] coefficientMultiplier

lemma coefficientMultiplier_comp_of_value_product
    (hcalc : FixedSobolevCalculus) (k : ℕ) (F G H : SmoothCoefficientJets (k+1))
    (hFG : coefficientValue (k+1) H = fun x => coefficientValue (k+1) F x * coefficientValue (k+1) G x) :
    (coefficientMultiplier hcalc k F).comp (coefficientMultiplier hcalc k G) =
      coefficientMultiplier hcalc k H := by
  apply ContinuousLinearMap.ext
  intro U
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k F (coefficientMultiplier hcalc k G U),
    coefficientMultiplier_value_ae hcalc k G U,coefficientMultiplier_value_ae hcalc k H U]
    with x hF hG hH
  change TauCeti.Wkp.value k (coefficientMultiplier hcalc k F (coefficientMultiplier hcalc k G U)) x =
    TauCeti.Wkp.value k (coefficientMultiplier hcalc k H U) x
  rw [hF,hG,hH,congrFun hFG x,mul_assoc]

end OAI.AnisotropicCalderon.DirichletFamily
namespace OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

attribute [local irreducible] coefficientMultiplier nativeThreeHalfCoefficientMulL
  nativeThreeHalfValueTraceL harmonicLiftCompletion

lemma nativeThreeHalfCoefficientMulL_comp_of_value_product
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F G H : SmoothCoefficientJets 3)
    (hFG : coefficientValue 3 H = fun x => coefficientValue 3 F x * coefficientValue 3 G x) :
    (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 H := by
  apply ContinuousLinearMap.ext
  intro f
  let U := harmonicLiftCompletion hF f
  let T := nativeThreeHalfValueTraceL hcalc hF hO hD τ0
  let MF := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 F
  have hG : T (coefficientMultiplier hcalc 2 G U) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 G f := by
    unfold nativeThreeHalfCoefficientMulL
    rfl
  have hH : T (coefficientMultiplier hcalc 2 H U) =
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 H f := by
    unfold nativeThreeHalfCoefficientMulL
    rfl
  have hOuter := nativeThreeHalfValueTraceL_coefficientMultiplier hcalc hF hO hD τ0 F
    (coefficientMultiplier hcalc 2 G U)
  have hBulk := congrArg (fun A : BallSobolev 2 →L[ℝ] BallSobolev 2 => A U)
    (coefficientMultiplier_comp_of_value_product hcalc 2 F G H hFG)
  exact (congrArg MF hG.symm).trans (hOuter.symm.trans ((congrArg T hBulk).trans hH))

end OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

#print axioms OAI.AnisotropicCalderon.DirichletFamily.coefficientMultiplier_comp_of_value_product
#print axioms OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier.nativeThreeHalfCoefficientMulL_comp_of_value_product
