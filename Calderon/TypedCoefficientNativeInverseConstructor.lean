import Calderon.UnitBallCoefficientOperatorSignature
import Calderon.NativeCoefficientWeakInverse
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def unitBallCoefficientNativeInverse
    (C : Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero :=
  nativeZeroFunctionalInverse (unitBallCoefficientEnergyL C)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.unitBallCoefficientNativeInverse
