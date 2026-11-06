import Calderon.NativeValueRadialTrace

/-! The kernel property of the value trace, a standard property from the literature. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic

/-- Kernel property for the value trace on the unit ball: its kernel is exactly the
zero-trace space `W^{1,2}_0`. -/
def UnitBallValueTraceKernel (τ0 : UnitBallValueTrace) : Prop :=
  ∀ u : BallH1, τ0.valueTraceL u = 0 ↔
    u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.UnitBallValueTraceKernel
