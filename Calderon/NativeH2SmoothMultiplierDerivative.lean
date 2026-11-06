import Calderon.NativeCoefficientH1ProductDerivative
import Calderon.NativeH2CoordinateProduct
import Calderon.NativeThreeHalfCoefficientMultiplier

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-H2-multiplier-derivative-v008.md. The product is the existing actual
coefficientMultiplier. No derivative or boundary regularity premise is added. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def smoothMultiplierLowerJets (Q : SmoothCoefficientJets 3) : SmoothCoefficientJets 2 :=
  compactCoefficient 2 (coefficientValue 3 Q) (contDiff_coefficientValue 3 Q)
    (hasCompactSupport_coefficientValue 3 Q)

lemma coefficientValue_smoothMultiplierLowerJets (Q : SmoothCoefficientJets 3) :
    coefficientValue 2 (smoothMultiplierLowerJets Q) = coefficientValue 3 Q :=
  coefficientValue_compactCoefficient 2 (coefficientValue 3 Q)
    (contDiff_coefficientValue 3 Q) (hasCompactSupport_coefficientValue 3 Q)

def smoothMultiplierDerivativeJets (Q : SmoothCoefficientJets 3) (i : Fin 3) :
    SmoothCoefficientJets 2 :=
  compactCoefficient 2
    (fun x => fderiv ℝ (coefficientValue 3 Q) x (MetricVolume.coordinateVector i))
    (((contDiff_coefficientValue 3 Q).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
    ((hasCompactSupport_coefficientValue 3 Q).fderiv_apply ℝ (MetricVolume.coordinateVector i))

lemma coefficientValue_smoothMultiplierDerivativeJets
    (Q : SmoothCoefficientJets 3) (i : Fin 3) :
    coefficientValue 2 (smoothMultiplierDerivativeJets Q i) =
      fun x => (gradient (coefficientValue 3 Q) x) i := by
  rw [smoothMultiplierDerivativeJets, coefficientValue_compactCoefficient]
  funext x
  simp only [MetricVolume.gradient_coordinate]

lemma firstOrder_H2SmoothMultiplier_eq_H1Product
    (hcalc : FixedSobolevCalculus) (Q : SmoothCoefficientJets 3) (U : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 1 (coefficientMultiplier hcalc 2 Q U) =
      nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q)
        (TauCeti.Wkp.firstOrder 1 U) := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc 2 Q U,
    nativeCoefficientH1ProductL_value_ae hcalc (smoothMultiplierLowerJets Q)
      (TauCeti.Wkp.firstOrder 1 U)] with x hleft hright
  rw [hleft, hright, coefficientValue_smoothMultiplierLowerJets,
    TauCeti.Wkp.value_firstOrder]

attribute [local irreducible] nativeCoefficientH1ProductL coefficientMultiplier
  unitBallCoordinateDerivativeL unitBallCoordinateGradientL
  smoothMultiplierLowerJets smoothMultiplierDerivativeJets

lemma coordinateDerivative_H2SmoothMultiplier
    (hcalc : FixedSobolevCalculus) (Q : SmoothCoefficientJets 3)
    (i : Fin 3) (U : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 0
      (unitBallCoordinateDerivativeL hcalc 1 i (coefficientMultiplier hcalc 2 Q U)) =
      nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q)
        (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)) +
      nativeCoefficientH1ProductL hcalc (smoothMultiplierDerivativeJets Q i)
        (TauCeti.Wkp.firstOrder 1 U) := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder, unitBallCoordinateDerivative_eq_coordinateGradient,
    firstOrder_H2SmoothMultiplier_eq_H1Product]
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  let d : BallH1 := TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 i U)
  have hd : TauCeti.W1p.value d = unitBallCoordinateGradientL i u :=
    (TauCeti.Wkp.value_firstOrder 0 _).trans
      (unitBallCoordinateDerivative_eq_coordinateGradient hcalc 1 i U)
  apply Lp.ext
  filter_upwards [nativeCoefficientH1ProductL_coordinateGradient_ae hcalc
      (smoothMultiplierLowerJets Q) u i,
    nativeH1Value_add_ae
      (nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q) d)
      (nativeCoefficientH1ProductL hcalc (smoothMultiplierDerivativeJets Q i) u),
    nativeCoefficientH1ProductL_value_ae hcalc (smoothMultiplierLowerJets Q) d,
    nativeCoefficientH1ProductL_value_ae hcalc (smoothMultiplierDerivativeJets Q i) u,
    unitBallCoordinateGradientL_ae i u] with x hleft hadd hq hder hgrad
  have hdx : TauCeti.W1p.value d x = unitBallCoordinateGradientL i u x :=
    congrArg (fun f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => f x) hd
  have hqv : coefficientValue 2 (smoothMultiplierLowerJets Q) x = coefficientValue 3 Q x :=
    congrFun (coefficientValue_smoothMultiplierLowerJets Q) x
  have hqg : (gradient (coefficientValue 2 (smoothMultiplierLowerJets Q)) x) i =
      (gradient (coefficientValue 3 Q) x) i :=
    congrArg (fun f : R3 → ℝ => (gradient f x) i)
      (coefficientValue_smoothMultiplierLowerJets Q)
  have hiv : coefficientValue 2 (smoothMultiplierDerivativeJets Q i) x =
      (gradient (coefficientValue 3 Q) x) i :=
    congrFun (coefficientValue_smoothMultiplierDerivativeJets Q i) x
  have hqNorm : TauCeti.W1p.value
      (nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q) d) x =
      coefficientValue 3 Q x * (TauCeti.W1p.gradient u x) i :=
    hq.trans (congrArg₂ (fun a b : ℝ => a*b) hqv (hdx.trans hgrad))
  have hiNorm : TauCeti.W1p.value
      (nativeCoefficientH1ProductL hcalc (smoothMultiplierDerivativeJets Q i) u) x =
      TauCeti.W1p.value u x * (gradient (coefficientValue 3 Q) x) i :=
    hder.trans ((congrArg (fun a : ℝ => a * TauCeti.W1p.value u x) hiv).trans
      (mul_comm _ _))
  have hsumNorm := hadd.trans (congrArg₂ (fun a b : ℝ => a+b) hqNorm hiNorm)
  have hleftNorm := hleft.trans (congrArg₂ (fun a b : ℝ => a+b)
    (congrArg (fun a : ℝ => a * (TauCeti.W1p.gradient u x) i) hqv)
    (congrArg (fun a : ℝ => TauCeti.W1p.value u x * a) hqg))
  exact hleftNorm.trans hsumNorm.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierLowerJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_smoothMultiplierLowerJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierDerivativeJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_smoothMultiplierDerivativeJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_H2SmoothMultiplier_eq_H1Product
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateDerivative_H2SmoothMultiplier
