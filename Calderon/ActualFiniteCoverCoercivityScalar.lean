import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask.MainPhysicalCoercivityAssembly

universe u

/-- A finite family of positive thresholds has one positive lower threshold,
also bounded by one; the index type is allowed to be empty. -/
lemma exists_pos_le_one_and_forall_le
    {ι : Type u} [Fintype ι] (d : ι → ℝ) (hd : ∀ i,0<d i) :
    ∃ eta : ℝ,0<eta ∧ eta≤1 ∧ ∀ i,eta≤d i := by
  classical
  have hMinimum (s : Finset ι) :
      ∃ eta : ℝ,0<eta ∧ eta≤1 ∧ ∀ i∈s,eta≤d i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,le_rfl,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨eta,heta,heta1,hAll⟩ := ih
      refine ⟨min eta (d i),lt_min heta (hd i),(min_le_left _ _).trans heta1,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji|hjs
      · subst j
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (hAll j hjs)
  obtain ⟨eta,heta,heta1,hAll⟩ := hMinimum Finset.univ
  exact ⟨eta,heta,heta1,fun i => hAll i (Finset.mem_univ i)⟩

/-- The literal positive remainder threshold used by the physical consumer.
All coefficient signs are numerical hypotheses supplied by actual factories. -/
lemma remainder_absorption_budget
    (CE CRem cRaise : ℝ) (hCE : 0≤CE) (hRem : 0≤CRem) (hc : 0<cRaise) :
    let etaAbs : ℝ := cRaise/(2*(CE+CRem+1))
    0<etaAbs ∧ ∀ eta : ℝ,0≤eta → eta≤etaAbs → (CE+CRem)*eta≤cRaise/2 := by
  dsimp only
  have hDen : 0<2*(CE+CRem+1) := by positivity
  refine ⟨div_pos hc hDen,?_⟩
  intro eta heta hCap
  have hMul : eta*(2*(CE+CRem+1))≤cRaise := (le_div_iff₀ hDen).mp hCap
  nlinarith only [hMul,heta]

/-- Exact finite-cover scalar absorption, with the original two beta budgets.
The sums need no sign assumptions. Neither N nor Q is divided by. -/
lemma finite_cover_scalar_coercivity
    (N Q cRaise BF IE IV sumIE sumIW : ℝ)
    (hN : 0≤N) (hQ : 0≤Q) (hc : 0<cRaise) (hIE : 0≤IE) (hIV : 0≤IV)
    (hFloor : 1+32*(max 1 N)^2*Q/cRaise≤BF)
    (hEnergy : IE≤N*sumIE)
    (hLocal : (cRaise/8)*sumIE≤sumIW)
    (hOutput : sumIW≤2*IV+(2*N*Q/BF)*IE) :
    0<cRaise/(32*(max 1 N)) ∧ (cRaise/(32*(max 1 N)))*IE≤IV := by
  let n : ℝ := max 1 N
  have hn : 1≤n := le_max_left _ _
  have hNn : N≤n := le_max_right _ _
  have hn0 : 0<n := zero_lt_one.trans_le hn
  have hFraction : 0≤32*n^2*Q/cRaise := by positivity
  have hFloorN : 1+32*n^2*Q/cRaise≤BF := hFloor
  have hBF1 : 1≤BF := by linarith only [hFloorN,hFraction]
  have hBF0 : 0<BF := zero_lt_one.trans_le hBF1
  have hFloor' : 32*n^2*Q/cRaise≤BF := by linarith only [hFloorN]
  have hFloorMul : 32*n^2*Q≤BF*cRaise := (div_le_iff₀ hc).mp hFloor'
  have hNSq : N^2≤n^2 := pow_le_pow_left₀ hN hNn 2
  have hNSqQ : N^2*Q≤n^2*Q := mul_le_mul_of_nonneg_right hNSq hQ
  have hNumerator : 2*N^2*Q≤(cRaise/16)*BF := by
    nlinarith only [hFloorMul,hNSqQ]
  have hErrorCoefficient : 2*N^2*Q/BF≤cRaise/16 :=
    (div_le_iff₀ hBF0).2 hNumerator
  have hCombined : (cRaise/8)*IE≤2*N*IV+(2*N^2*Q/BF)*IE := by
    calc
      _ ≤ (cRaise/8)*(N*sumIE) :=
        mul_le_mul_of_nonneg_left hEnergy (div_nonneg hc.le (by norm_num))
      _ = N*((cRaise/8)*sumIE) := by ring
      _ ≤ N*sumIW := mul_le_mul_of_nonneg_left hLocal hN
      _ ≤ N*(2*IV+(2*N*Q/BF)*IE) := mul_le_mul_of_nonneg_left hOutput hN
      _ = _ := by ring
  have hErrorTerm := mul_le_mul_of_nonneg_right hErrorCoefficient hIE
  have hOutputTerm : 2*N*IV≤2*n*IV := by
    nlinarith only [mul_le_mul_of_nonneg_right hNn hIV]
  have hAbsorbed : (cRaise/16)*IE≤2*n*IV := by
    nlinarith only [hCombined,hErrorTerm,hOutputTerm]
  have hLast : cRaise*IE≤IV*(32*n) := by nlinarith only [hAbsorbed]
  refine ⟨div_pos hc (mul_pos (by norm_num) hn0),?_⟩
  calc
    _ = (cRaise*IE)/(32*n) := by ring
    _ ≤ IV := (div_le_iff₀ (mul_pos (by norm_num) hn0)).2 hLast

end OAI.AnisotropicCalderon.MixedKernelConstructionTask.MainPhysicalCoercivityAssembly
