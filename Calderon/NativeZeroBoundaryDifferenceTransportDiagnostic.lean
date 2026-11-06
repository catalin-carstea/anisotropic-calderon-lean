import Calderon.NativeCoefficientWeakHalfLift

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

lemma nativeZeroBoundaryDifference_transport (u uprime v : BallH1)
    (he : u=uprime)
    (hzero : u-v ∈ TauCeti.w1p0Submodule volume ballOpens 2) :
    uprime-v ∈ TauCeti.w1p0Submodule volume ballOpens 2 :=
  (congrArg (fun z : BallH1 => z-v ∈ TauCeti.w1p0Submodule volume ballOpens 2) he).mp hzero

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeZeroBoundaryDifference_transport
