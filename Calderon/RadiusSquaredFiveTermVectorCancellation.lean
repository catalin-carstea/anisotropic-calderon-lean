import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily

lemma pow_smul_ordered_five_term_vector_sum
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (power : ℕ) (r f : ℝ) (a e : V) (b c d : Fin 3 → V) :
    r^power • (a+(∑ j : Fin 3, b j)+r • (∑ j : Fin 3, c j)+
      r^2 • (∑ j : Fin 3, d j)+(r*f) • e) =
      r^power • a+(∑ j : Fin 3, r^power • b j)+
      (∑ j : Fin 3, r^(power+1) • c j)+
      (∑ j : Fin 3, (r^power*r^2) • d j)+(f*r^(power+1)) • e := by
  simp only [smul_add,Finset.smul_sum,smul_smul,pow_succ]
  match_scalars <;> ring

lemma eq_ordered_five_term_vector_sum_of_sq_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r f : ℝ) (q a e : V) (b c d : Fin 3 → V) (hr : r ≠ 0)
    (hSquare : r^2 • q = r^2 • a+(∑ j : Fin 3, r^2 • b j)+
      (∑ j : Fin 3, r^3 • c j)+
      (∑ j : Fin 3, (r^2*r^2) • d j)+(f*r^3) • e) :
    q = a+(∑ j : Fin 3, b j)+r • (∑ j : Fin 3, c j)+
      r^2 • (∑ j : Fin 3, d j)+(r*f) • e := by
  let W : V := a+(∑ j : Fin 3, b j)+r • (∑ j : Fin 3, c j)+
    r^2 • (∑ j : Fin 3, d j)+(r*f) • e
  have hFactor := pow_smul_ordered_five_term_vector_sum 2 r f a e b c d
  have hScaled : r^2 • q = r^2 • W := hSquare.trans hFactor.symm
  have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr
  have hCancel := congrArg (fun v : V => (r^2)⁻¹ • v) hScaled
  exact (by simpa only [inv_smul_smul₀ hr2] using hCancel)

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.pow_smul_ordered_five_term_vector_sum
#print axioms OAI.AnisotropicCalderon.DirichletFamily.eq_ordered_five_term_vector_sum_of_sq_eq
