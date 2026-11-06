import Calderon.NativeValueRadialTrace

/-! Full upfront: day-oct13/native-trace-kernel-literature-oct15-v001/EXPANSION.md.
Proposed standard literature property only; no inhabitant or axiom. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic

/-- Exact kernel property for the existing value trace on the actual unit ball.
Source adoption requires independent reviews and explicit reconciliation. -/
def UnitBallValueTraceKernel (τ0 : UnitBallValueTrace) : Prop :=
  ∀ u : BallH1, τ0.valueTraceL u = 0 ↔
    u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2

end OAI.AnisotropicCalderon.DirichletFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.UnitBallValueTraceKernel
