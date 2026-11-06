import Mathlib.Algebra.Module.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace OAI.AnisotropicCalderon.ActualReferenceFirstRotationCollection

lemma first_base_fixed_rotation_collection
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (r : ℝ) (q gamma eta : Fin 3 → Fin 3 → ℝ) (e : Fin 3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ) (I J : M) (T : Fin 3 → Fin 3 → M) :
    r • (∑ a : Fin 3, ∑ b : Fin 3, q a b •
      ((-gamma a b) • I +
        e a • ((1/2 : ℝ) • (∑ s : Fin 3, ∑ t : Fin 3, Gamma b s t • T s t)) +
        e b • ((1/2 : ℝ) • (∑ s : Fin 3, ∑ t : Fin 3, Gamma a s t • T s t)) +
        eta a b • J)) =
      (-r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*gamma a b)) • I +
      (r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*eta a b)) • J +
      (∑ s : Fin 3, ∑ t : Fin 3,
        ((1/2 : ℝ)*r*(∑ a : Fin 3, ∑ b : Fin 3,
          q a b*(e a*Gamma b s t+e b*Gamma a s t))) • T s t) := by
  have hmove (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → M) :
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ s : Fin 3, ∑ t : Fin 3, f a b s t) =
      (∑ s : Fin 3, ∑ t : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, f a b s t) := by
    calc
      _ = ∑ a : Fin 3, ∑ s : Fin 3, ∑ b : Fin 3, ∑ t : Fin 3, f a b s t := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑ s : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3, ∑ t : Fin 3, f a b s t := Finset.sum_comm
      _ = ∑ s : Fin 3, ∑ a : Fin 3, ∑ t : Fin 3, ∑ b : Fin 3, f a b s t := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        exact Finset.sum_comm
  have hrot (v : Fin 3 → Fin 3 → ℝ) (H : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
      r • (∑ a : Fin 3, ∑ b : Fin 3, q a b •
        (v a b • ((1/2 : ℝ) • (∑ s : Fin 3, ∑ t : Fin 3, H a b s t • T s t)))) =
      (∑ s : Fin 3, ∑ t : Fin 3,
        ((1/2 : ℝ)*r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*v a b*H a b s t)) • T s t) := by
    simp only [Finset.smul_sum,Finset.sum_smul,Finset.mul_sum,smul_smul]
    rw [hmove]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    ring
  have hscalar : r • (∑ a : Fin 3, ∑ b : Fin 3, q a b • ((-gamma a b) • I)) =
      (-r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*gamma a b)) • I := by
    simp only [Finset.sum_smul,Finset.smul_sum,Finset.mul_sum,smul_smul,mul_assoc,mul_neg,neg_mul,neg_smul,smul_neg,
      Finset.sum_neg_distrib]
  have hdegree : r • (∑ a : Fin 3, ∑ b : Fin 3, q a b • (eta a b • J)) =
      (r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*eta a b)) • J := by
    simp only [Finset.sum_smul,Finset.smul_sum,Finset.mul_sum,smul_smul,mul_assoc]
  have hcombine :
      (∑ s : Fin 3, ∑ t : Fin 3,
        ((1/2 : ℝ)*r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*e a*Gamma b s t)) • T s t) +
      (∑ s : Fin 3, ∑ t : Fin 3,
        ((1/2 : ℝ)*r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*e b*Gamma a s t)) • T s t) =
      (∑ s : Fin 3, ∑ t : Fin 3,
        ((1/2 : ℝ)*r*(∑ a : Fin 3, ∑ b : Fin 3,
          q a b*(e a*Gamma b s t+e b*Gamma a s t))) • T s t) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← add_smul]
    congr 1
    simp only [mul_add,Finset.sum_add_distrib,mul_assoc]
  simp only [smul_add,Finset.sum_add_distrib]
  rw [hscalar,hdegree,hrot (fun a _ => e a) (fun _ b => Gamma b),
    hrot (fun _ b => e b) (fun a _ => Gamma a)]
  calc
    _ = (-r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*gamma a b)) • I +
        (r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*eta a b)) • J +
        ((∑ s : Fin 3, ∑ t : Fin 3,
          ((1/2 : ℝ)*r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*e a*Gamma b s t)) • T s t) +
        (∑ s : Fin 3, ∑ t : Fin 3,
          ((1/2 : ℝ)*r*(∑ a : Fin 3, ∑ b : Fin 3, q a b*e b*Gamma a s t)) • T s t)) := by abel
    _ = _ := by rw [hcombine]

end OAI.AnisotropicCalderon.ActualReferenceFirstRotationCollection
