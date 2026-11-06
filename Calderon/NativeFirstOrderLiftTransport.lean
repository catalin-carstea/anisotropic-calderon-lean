import Calderon.StrongDirichletDomain

/-! EXPANSION.json precedes literal actual native lift-existential equality transport. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

lemma nativeFirstOrderLift_transport
    (k : ℕ) (u v : BallH1) (h : u = v)
    (hLift : ∃ U : BallSobolev (k+1), TauCeti.Wkp.firstOrder k U = u) :
    ∃ U : BallSobolev (k+1), TauCeti.Wkp.firstOrder k U = v := by
  cases h
  exact hLift

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.nativeFirstOrderLift_transport
