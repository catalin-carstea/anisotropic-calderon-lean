import Calderon.ActualReferenceAdjointH3Operator
import Calderon.NativeScalarMassPrincipalRegularity
import Calderon.NativeCoefficientMultiplierOrderCoherence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma value_adjointMass_one_eq_zero_of_same_coefficient
    (hcalc : FixedSobolevCalculus)
    (M2 : SmoothCoefficientJets 2) (M1 : SmoothCoefficientJets 1)
    (hValue : coefficientValue 2 M2 = coefficientValue 1 M1)
    (E : BallSobolev 2) :
    TauCeti.Wkp.value 1
      (coefficientMultiplier hcalc 1 M2 (nativeLowerOrderL 1 E)) =
      TauCeti.Wkp.value 0
        (nativeCoefficientMassL hcalc M1 (nativeH2FirstOrderL E)) := by
  have h := lowerOrder_coefficientMultiplier_of_value_eq hcalc 0 M2 M1 hValue
    (nativeLowerOrderL 1 E)
  have hArg : TauCeti.Wkp.lowerOrder 0 (nativeLowerOrderL 1 E) =
      TauCeti.W1p.value (nativeH2FirstOrderL E) := by
    rfl
  rw [TauCeti.Wkp.value_succ 0]
  rw [h,hArg]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
