import Calderon.ActualHigherSPhysicalPairing
/-! Typed direct-term algebra. -/
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectAlgebra

section Generic
variable {E H N Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- Only the high/low graph is needed for a first/linear pairing. -/
lemma first_physical_inner_eq_low_sum
    (I : E →L[ℝ] H) (J : H →L[ℝ] N) (K : H →L[ℝ] Q)
    (P : H →L[ℝ] N →L[ℝ] ℝ)
    (hPair : ∀ v z : H,P v (J z)=⟪K v,K z⟫_ℝ)
    (A : Fin 3 → E →L[ℝ] H) (Low : Fin 3 → H →L[ℝ] N)
    (v : Fin 3 → E) (u : Fin 3 → H)
    (hGraph : ∀ i,J (A i (v i))=Low i (I (v i))) (hInput : ∀ i,I (v i)=u i)
    (z : H) : ⟪K (∑ i : Fin 3,A i (v i)),K z⟫_ℝ=∑ i : Fin 3,P z (Low i (u i)) := by
  rw [real_inner_comm,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (hPair z (A i (v i))).symm.trans
    (congrArg (fun n : N => P z n) ((hGraph i).trans (congrArg (Low i) (hInput i))))

/-- Move only the OUTER word atom; no lift of a gained output is used. -/
lemma word_physical_inner_eq_low_sum {AIdx WIdx : Type*} [Fintype WIdx]
    (I : E →L[ℝ] H) (J : H →L[ℝ] N) (K : H →L[ℝ] Q)
    (P : H →L[ℝ] N →L[ℝ] ℝ)
    (hPair : ∀ v z : H,P v (J z)=⟪K v,K z⟫_ℝ)
    (A : AIdx → E →L[ℝ] H) (Low : AIdx → H →L[ℝ] N)
    (first second : WIdx → AIdx) (c : WIdx → ℝ) (U : E) (V : AIdx → E)
    (hGraph : ∀ a v,J (A a v)=Low a (I v))
    (hLift : ∀ a,I (V a)=A a U) (z : H) :
    ⟪K (∑ w : WIdx,c w • A (first w) (V (second w))),K z⟫_ℝ=
      ∑ w : WIdx,c w*P z (Low (first w) (A (second w) U)) := by
  rw [real_inner_comm,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_smul,inner_smul_right]
  exact congrArg (fun n : ℝ => c w*n)
    ((hPair z (A (first w) (V (second w)))).symm.trans
      (congrArg (fun n : N => P z n)
        ((hGraph _ _).trans (congrArg (Low _) (hLift _)))))

lemma abs_pair_low_input_le (P : H →L[ℝ] N →L[ℝ] ℝ) (Low : H →L[ℝ] N)
    (z v : H) (Z B : ℝ) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hz : ‖z‖ ≤ Z) (hLow : ‖Low‖ ≤ B) :
    |P z (Low v)| ≤ ‖P‖*Z*B*‖v‖ := by
  have hLv : ‖Low v‖ ≤ B*‖v‖ := (Low.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hLow (norm_nonneg _))
  calc
    _ ≤ ‖P‖*‖z‖*‖Low v‖ := by
      simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P z (Low v)
    _ ≤ ‖P‖*Z*(B*‖v‖) := mul_le_mul
      (mul_le_mul_of_nonneg_left hz (norm_nonneg P)) hLv (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma abs_pair_low_high_le (P : H →L[ℝ] N →L[ℝ] ℝ) (Low : H →L[ℝ] N)
    (High : E →L[ℝ] H) (z : H) (U : E) (Z B A : ℝ)
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hz : ‖z‖ ≤ Z) (hLow : ‖Low‖ ≤ B) (hHigh : ‖High‖ ≤ A) :
    |P z (Low (High U))| ≤ ‖P‖*Z*B*A*‖U‖ := by
  have h := abs_pair_low_input_le P Low z (High U) Z B hZ hB hz hLow
  have hAU : ‖High U‖ ≤ A*‖U‖ := (High.le_opNorm U).trans
    (mul_le_mul_of_nonneg_right hHigh (norm_nonneg _))
  exact h.trans ((mul_le_mul_of_nonneg_left hAU (by positivity)).trans (le_of_eq (by ring)))

lemma norm_physical_sq_le (K : H →L[ℝ] Q) (z : H) (Z : ℝ) (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z) :
    ‖K z‖^2 ≤ ‖K‖^2*Z^2 := by
  have h := (K.le_opNorm z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
  have hs := mul_le_mul h h (norm_nonneg _) (by positivity : 0 ≤ ‖K‖*Z)
  simpa only [← pow_two,mul_pow] using hs
end Generic

lemma abs_weighted_sum_le {I : Type*} [Fintype I] (c f : I → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i,|f i| ≤ B) : |∑ i : I,c i*f i| ≤ (∑ i : I,|c i|)*B := by
  calc
    _ ≤ ∑ i : I,|c i*f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : I,|c i| * B := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

lemma abs_three_sum_le (a b c : ℝ) : |a+b+c| ≤ |a|+|b|+|c| :=
  (abs_add_le (a+b) c).trans (add_le_add (abs_add_le a b) (le_refl |c|))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDirectAlgebra
