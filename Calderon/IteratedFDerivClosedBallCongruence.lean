import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma iteratedFDeriv_eq_of_eqOn_uniqueDiffOn
    {f g : E → V} {s : Set E} {x : E} (hfg : EqOn f g s)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (n : ℕ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  exact (iteratedFDerivWithin_eq_iteratedFDeriv hs hf hx).symm.trans
    ((iteratedFDerivWithin_congr hfg hx n).trans
      (iteratedFDerivWithin_eq_iteratedFDeriv hs hg hx))

lemma iteratedFDeriv_eq_of_eqOn_closedBall
    {f g : E → V} (c : E) (r : ℝ) (hr : 0 < r)
    (hfg : EqOn f g (closedBall c r)) {x : E} (hx : x ∈ closedBall c r) (n : ℕ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x := by
  have hs : UniqueDiffOn ℝ (closedBall c r) :=
    uniqueDiffOn_convex (convex_closedBall c r)
      ⟨c, ball_subset_interior_closedBall (mem_ball_self hr)⟩
  exact iteratedFDeriv_eq_of_eqOn_uniqueDiffOn hfg hs hx n hf hg

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.iteratedFDeriv_eq_of_eqOn_uniqueDiffOn
#print axioms OAI.AnisotropicCalderon.DirichletFamily.iteratedFDeriv_eq_of_eqOn_closedBall
