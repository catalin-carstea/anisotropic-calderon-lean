import Calderon.CollaboratorUCPLocalOct17

/-! # Weak unique continuation

The proof of `uniqueContinuation` (Carleman estimate in `UCPCarleman.lean`, local step and
connectedness in `UCPLocal.lean`) follows Le Rousseau–Lebeau, *On Carleman estimates for elliptic
and parabolic operators*, ESAIM COCV 18 (2012), §§3–4, with an elementary
(Fursikov–Imanuvilov style) integration-by-parts proof of the Carleman estimate. -/

noncomputable section
namespace OAI.AnisotropicCalderon

/-- Weak unique continuation for `div(A ∇u) = 0`. -/
theorem uniqueContinuation : UniqueContinuation := UCP.uniqueContinuation_aux

end OAI.AnisotropicCalderon
