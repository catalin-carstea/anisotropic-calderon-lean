import Calderon.RealNormedSpaceUniquenessBridge

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

universe u

lemma contDiff_real_carrier_transport
    {P : Type*} {E F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : NormedAddCommGroup E) (h : NormedAddCommGroup F)
    (s : @NormedSpace ℝ E _ g.toSeminormedAddCommGroup)
    (t : @NormedSpace ℝ F _ h.toSeminormedAddCommGroup)
    (e : E = F) (hg : HEq g h) (f : P → E) (k : P → F)
    (hf : HEq f k) (hc : letI := g; letI := s; ContDiff ℝ ∞ f) :
    letI := h; letI := t; ContDiff ℝ ∞ k := by
  subst F
  have hgh : g = h := eq_of_heq hg
  cases hgh
  letI := g
  cases real_normedSpace_eq s t
  have hfk : f = k := eq_of_heq hf
  cases hfk
  exact hc

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
