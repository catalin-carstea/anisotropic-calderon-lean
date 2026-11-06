import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! EXPANSION.json precedes the constructor-free Cauchy sequence transport. -/
set_option autoImplicit false
noncomputable section
open Filter
namespace OAI.AnisotropicCalderon.ExteriorSource

theorem cauchySeq_of_eventual_sq_norm_sub_le_mul
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (u : ℕ → X) (v : ℕ → Y) (C : ℝ) (hC : 0 ≤ C) (N0 : ℕ)
    (hValue : CauchySeq v)
    (hBound : ∀ m ≥ N0, ∀ n ≥ N0, ‖u m-u n‖^2 ≤ C * ‖v m-v n‖^2) :
    CauchySeq u := by
  have hD : 0 < C+1 := by linarith
  apply Metric.cauchySeq_iff.2
  intro ε hε
  obtain ⟨N1,hN1⟩ := Metric.cauchySeq_iff.1 hValue (ε/(C+1)) (div_pos hε hD)
  refine ⟨max N0 N1,?_⟩
  intro m hm n hn
  have hm0 : N0 ≤ m := (le_max_left _ _).trans hm
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hm1 : N1 ≤ m := (le_max_right _ _).trans hm
  have hn1 : N1 ≤ n := (le_max_right _ _).trans hn
  have hCD : C ≤ (C+1)^2 := by nlinarith [sq_nonneg C]
  have hsq : ‖u m-u n‖^2 ≤ ((C+1)*‖v m-v n‖)^2 := by
    calc
      _ ≤ C * ‖v m-v n‖^2 := hBound m hm0 n hn0
      _ ≤ (C+1)^2 * ‖v m-v n‖^2 := mul_le_mul_of_nonneg_right hCD (sq_nonneg _)
      _ = _ := by ring
  have hNorm : ‖u m-u n‖ ≤ (C+1)*‖v m-v n‖ :=
    le_of_sq_le_sq hsq (mul_nonneg hD.le (norm_nonneg _))
  have hSmall : ‖v m-v n‖ < ε/(C+1) := by simpa only [dist_eq_norm] using hN1 m hm1 n hn1
  rw [dist_eq_norm]
  exact hNorm.trans_lt (by
    have h := (lt_div_iff₀ hD).1 hSmall
    simpa only [mul_comm] using h)

end OAI.AnisotropicCalderon.ExteriorSource
