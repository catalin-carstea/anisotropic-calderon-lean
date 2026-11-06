import Calderon.UnitBallCoefficientOperatorSignature
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem continuous_unitBallCoefficientEnergyL_curve
    (C : ℝ → Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens)) (hC : Continuous C) :
    Continuous (fun R : ℝ => unitBallCoefficientEnergyL (C R)) :=
  unitBallCoefficientEnergyL.continuous.comp hC

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_unitBallCoefficientEnergyL_curve
