import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZeroCoefficientLinearity
variable {V H N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem forward_zero_split (J : H →L[ℝ] N) (r : ℝ)
    (Q : Fin 3 → Fin 3 → ℝ) (b f : Fin 3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (E : Fin 3 → V →L[ℝ] H) (D : Fin 3 → Fin 3 → V →L[ℝ] H)
    (T : Fin 3 → Fin 3 → V →L[ℝ] N) (R S : V →L[ℝ] N) :
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (J.comp (D i j)+T i j+f i • J.comp (E j)-
          ∑ k : Fin 3, Gamma i k j • J.comp (E k)))+
      r^2 • (∑ i : Fin 3, b i • J.comp (E i)))+R)+S =
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • T i j)+R)+S)+
      J.comp (r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k))+
        r^2 • (∑ i : Fin 3, b i • E i)) := by
  ext u
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sub,map_sum,map_smul,smul_add,smul_sub,Finset.smul_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

theorem reverse_zero_row (J : H →L[ℝ] N) (L : H →L[ℝ] N)
    (OH DH ei ej d : V →L[ℝ] H) (OL DL : H →L[ℝ] N)
    (fi fj : ℝ) (Gamma : Fin 3 → ℝ) (E : Fin 3 → V →L[ℝ] H) :
    -L.comp (OH+fi • DH)+(2*fi) • L.comp DH-J.comp d-
      (OL+fj • DL).comp ei+(2*fj) • DL.comp ei+fi • J.comp ej-
      (∑ k : Fin 3, Gamma k • J.comp (E k)) =
    L.comp (-OH+fi • DH)+(-OL+fj • DL).comp ei+
      J.comp (-d+fi • ej-∑ k : Fin 3, Gamma k • E k) := by
  ext u
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sub,map_neg,map_sum,map_smul,smul_add,smul_sub,smul_neg,Finset.smul_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib,neg_add,neg_sub]
  module

theorem reverse_zero_split (J : H →L[ℝ] N) (r : ℝ)
    (Q : Fin 3 → Fin 3 → ℝ) (b f : Fin 3 → ℝ)
    (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ) (d1 d2 : Fin 3 → Fin 3 → ℝ)
    (E : Fin 3 → V →L[ℝ] H) (D : Fin 3 → Fin 3 → V →L[ℝ] H)
    (T : Fin 3 → Fin 3 → V →L[ℝ] N) (R S : V →L[ℝ] N) :
    (((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (T i j+J.comp (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k)))-
      ∑ i : Fin 3, ∑ j : Fin 3,
        (d1 i j • J.comp (E j)+d2 i j • J.comp (E i)))+
      r^2 • (∑ i : Fin 3, b i • J.comp (E i)))+R)+S =
    ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j • T i j)+R)+S)+
      J.comp ((r^2 • (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
        (D i j+f i • E j-∑ k : Fin 3, Gamma i k j • E k))-
        ∑ i : Fin 3, ∑ j : Fin 3, (d1 i j • E j+d2 i j • E i))+
        r^2 • (∑ i : Fin 3, b i • E i)) := by
  ext u
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    map_add,map_sub,map_neg,map_sum,map_smul,smul_add,smul_sub,smul_neg,Finset.smul_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib,neg_add,neg_sub]
  abel
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZeroCoefficientLinearity
