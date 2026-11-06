import Calderon.NativeH3CoefficientConormalTrace
import Calderon.NativeH2SmoothMultiplierDerivative
import Calderon.NativeCoefficientFluxTrace
import Calderon.NativeZeroValueTrace
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Gradient ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
open NativeH3CoefficientConormalTrace


private theorem sphereContinuousScalarMulL_eq_self_of_one
    (c : C(UnitSphere, ℝ)) (hOne : ∀ x, c x = 1) (f : SphereL2) :
    sphereContinuousScalarMulL c f = f := by
  apply Lp.ext
  filter_upwards [sphereContinuousScalarMul_value_ae c f] with x hx
  change sphereContinuousScalarMul c f x = f x
  rw [hx,hOne x,one_mul]

private theorem nativeCoefficientH1ProductL_valueTrace
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (u : BallH1) :
    τ0.valueTraceL (nativeCoefficientH1ProductL hcalc F u) =
      sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData F)) (τ0.valueTraceL u) := by
  exact valueTraceL_firstOrder_coefficientMultiplier hcalc τ0 F u

attribute [local irreducible] nativeCoefficientH1ProductL coefficientMultiplier
  smoothMultiplierLowerJets smoothMultiplierDerivativeJets sphereContinuousScalarMulL
  strongCoordinateTraceL ordinaryConormalTraceL


theorem strongCoordinateTraceL_cutoff_zeroDirichlet
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (hOne : ∀ x : UnitSphere, coefficientValue 3 Q x.val = 1)
    (U : StrongDirichletSpace 0) (i : Fin 3) :
    strongCoordinateTraceL hcalc τ0 i (coefficientMultiplier hcalc 2 Q (U : BallSobolev 2)) =
      strongCoordinateTraceL hcalc τ0 i (U : BallSobolev 2) := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 (U : BallSobolev 2)
  let d : BallH1 := TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i (U : BallSobolev 2))
  have hZero : τ0.valueTraceL u = 0 := valueTraceL_eq_zero_of_mem_w1p0 τ0 u U.property
  have hOneLower : ∀ x : UnitSphere, smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q)) x = 1 := by
    intro x
    change coefficientValue 2 (smoothMultiplierLowerJets Q) x.val = 1
    rw [coefficientValue_smoothMultiplierLowerJets]
    exact hOne x
  have hD := coordinateDerivative_H2SmoothMultiplier hcalc Q i (U : BallSobolev 2)
  calc
    _ = τ0.valueTraceL (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i
        (coefficientMultiplier hcalc 2 Q (U : BallSobolev 2)))) :=
      strongCoordinateTraceL_apply hcalc τ0 i _
    _ = τ0.valueTraceL (nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q) d +
        nativeCoefficientH1ProductL hcalc (smoothMultiplierDerivativeJets Q i) u) := congrArg τ0.valueTraceL hD
    _ = τ0.valueTraceL (nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q) d) +
        τ0.valueTraceL (nativeCoefficientH1ProductL hcalc (smoothMultiplierDerivativeJets Q i) u) :=
      τ0.valueTraceL.map_add _ _
    _ = sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (smoothMultiplierLowerJets Q)))
        (τ0.valueTraceL d) +
      sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (smoothMultiplierDerivativeJets Q i)))
        (τ0.valueTraceL u) :=
      congrArg₂ (fun x y : SphereL2 => x+y)
        (nativeCoefficientH1ProductL_valueTrace hcalc τ0 (smoothMultiplierLowerJets Q) d)
        (nativeCoefficientH1ProductL_valueTrace hcalc τ0 (smoothMultiplierDerivativeJets Q i) u)
    _ = τ0.valueTraceL d + 0 :=
      congrArg₂ (fun x y : SphereL2 => x+y)
        (sphereContinuousScalarMulL_eq_self_of_one _ hOneLower _)
        ((congrArg (sphereContinuousScalarMulL
          (smoothSphereValue (coefficientSmoothData (smoothMultiplierDerivativeJets Q i)))) hZero).trans (map_zero _))
    _ = _ := (add_zero _).trans (strongCoordinateTraceL_apply hcalc τ0 i (U : BallSobolev 2)).symm

theorem ordinaryConormalTraceL_cutoff_zeroDirichlet
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3) (hOne : ∀ x : UnitSphere, coefficientValue 3 Q x.val = 1)
    (U : StrongDirichletSpace 0) :
    ordinaryConormalTraceL hcalc τ0 F (coefficientMultiplier hcalc 2 Q (U : BallSobolev 2)) =
      ordinaryConormalTraceL hcalc τ0 F (U : BallSobolev 2) := by
  rw [ordinaryConormalTraceL_eq_sphere_coefficient_trace hcalc τ0 F,
    ordinaryConormalTraceL_eq_sphere_coefficient_trace hcalc τ0 F]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun f : SphereL2 => sphereCoordinateMulL i
    (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F i j))) f))
    (strongCoordinateTraceL_cutoff_zeroDirichlet hcalc τ0 Q hOne U j)

theorem sphereSobolevInclusionL_zero_highConormal_eq_uncut_low
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientMatrix 3) (G : SmoothCoefficientMatrix 2)
    (hFG : ∀ i j, coefficientValue 3 (F i j) = coefficientValue 2 (G i j))
    (Q : SmoothCoefficientJets 3) (hOne : ∀ x : UnitSphere, coefficientValue 3 Q x.val = 1)
    (Z : BallSobolev 3) (U : StrongDirichletSpace 0)
    (hLower : TauCeti.Wkp.lowerOrder 2 Z = coefficientMultiplier hcalc 2 Q (U : BallSobolev 2)) :
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F Z) =
      sphereSobolevZeroEquiv hO hD (ordinaryConormalTraceL hcalc τ0 G (U : BallSobolev 2)) := by
  have hHigh := sphereSobolevInclusionL_zero_nativeThreeHalfCoefficientConormalTraceL
    hcalc hF hO hD τ0 F G hFG Z
  have hConormal : ordinaryConormalTraceL hcalc τ0 G (TauCeti.Wkp.lowerOrder 2 Z) =
      ordinaryConormalTraceL hcalc τ0 G (U : BallSobolev 2) :=
    (congrArg (ordinaryConormalTraceL hcalc τ0 G) hLower).trans
      (ordinaryConormalTraceL_cutoff_zeroDirichlet hcalc τ0 G Q hOne U)
  exact hHigh.trans (congrArg (sphereSobolevZeroEquiv hO hD) hConormal)

end OAI.AnisotropicCalderon.ConnectionError
