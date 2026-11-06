import Calderon.CollaboratorUCPIdentityOct17

/-! Exact product identities for the actual cutoff divergence operator.
Full before-code expansion: UPFRONT-NATIVE-DIVERGENCE-PRODUCT-RULE-v001.md. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon

theorem Lop_mul
    {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    {f h : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x : R3) :
    Lop a (fun y => f y * h y) x = f x * Lop a h x + h x * Lop a f x +
      ∑ i : Fin 3, ∑ j : Fin 3,
        (a i j x + a j i x) * pd i f x * pd j h x := by
  have : ∀ i j, ContDiff ℝ ∞ (fun y => a i j y) := ha
  unfold Lop
  simp (disch := fun_prop) only [pd_mul, pd_add, pd_sum]
  simp only [Fin.sum_univ_three]
  ring

theorem Lop_mul_of_symmetric
    {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hsymm : ∀ i j, a i j = a j i)
    {f h : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x : R3) :
    Lop a (fun y => f y * h y) x = f x * Lop a h x + h x * Lop a f x +
      2 * ∑ i : Fin 3, ∑ j : Fin 3, a i j x * pd i f x * pd j h x := by
  rw [Lop_mul ha hf hh x]
  simp only [Fin.sum_univ_three, hsymm 1 0, hsymm 2 0, hsymm 2 1]
  ring

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.Lop_mul
#print axioms OAI.AnisotropicCalderon.Lop_mul_of_symmetric
