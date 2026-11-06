import Calderon.ActualReferenceAdjointH3Operator
import Calderon.DirichletForcingInjectivity
import Calderon.OrdinaryWeightedDriftOperator

set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The actual divergence-form principal operator has the same L² value
when its H³ input and order-three jets are lowered to H²/order-two jets. -/
lemma value_ordinaryPrincipalL_one_eq_zero_of_same_matrix
    (hcalc : FixedSobolevCalculus) (F3 : SmoothCoefficientMatrix 3)
    (F2 : SmoothCoefficientMatrix 2)
    (hValue : coefficientMatrixField 3 F3 = coefficientMatrixField 2 F2)
    (U : BallSobolev 3) :
    TauCeti.Wkp.value 1 (ordinaryPrincipalL hcalc 1 F3 U) =
      TauCeti.Wkp.value 0
        (ordinaryPrincipalL hcalc 0 F2 (nativeLowerOrderL 2 U)) := by
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  have hHigh := ordinaryPrincipalL_energy hcalc 1 F3 U v
  have hLow := ordinaryPrincipalL_energy hcalc 0 F2 (nativeLowerOrderL 2 U) v
  rw [hHigh, hLow]
  rw [hValue]
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
