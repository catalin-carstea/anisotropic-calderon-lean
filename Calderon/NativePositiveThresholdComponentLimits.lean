import Calderon.NativeL2DominatedSquaredDifference
import Calderon.NativePositiveThresholdGradientFormula
import Calderon.PositiveThresholdIndicatorScalarLimit
import TauCeti.Analysis.Sobolev.W1p.LevelSet
import Mathlib.Analysis.SpecificLimits.Basic

/-! EXPANSION.json precedes actual positive-threshold native graph-norm convergence. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.EnergyBridge
attribute [local irreducible] TauCeti.W1p.posPartAbove TauCeti.W1p.posPart

theorem tendsto_nativeH1_posPartAbove_value_one_div_add (u : BallH1) :
    Tendsto (fun n : ℕ => TauCeti.W1p.value (TauCeti.W1p.posPartAbove
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity) u)) atTop
      (𝓝 (TauCeti.W1p.value (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u))) := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  let hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  let κ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hκPos : ∀ n, 0 < κ n := fun n => by dsimp only [κ]; positivity
  have hκ : Tendsto κ atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  let U : ℕ → BallH1 := fun n => TauCeti.W1p.posPartAbove hp (hκPos n).le u
  let U0 : BallH1 := TauCeti.W1p.posPart hp u
  have hV : ∀ n, TauCeti.W1p.value (U n) =ᵐ[μ]
      (fun x => max (TauCeti.W1p.value u x - κ n) 0) :=
    fun n => TauCeti.W1p.value_posPartAbove_ae hp (hκPos n).le u
  have hV0 : TauCeti.W1p.value U0 =ᵐ[μ] (fun x => max (TauCeti.W1p.value u x) 0) := by
    dsimp only [U0]
    rw [TauCeti.W1p.value_posPart]
    exact Lp.coeFn_posPart (TauCeti.W1p.value u)
  have hSubV : ∀ n, ⇑(TauCeti.W1p.value (U n) - TauCeti.W1p.value U0) =ᵐ[μ]
      (fun x => TauCeti.W1p.value (U n) x - TauCeti.W1p.value U0 x) :=
    fun n => (Lp.coeFn_sub _ _).mono (fun x hx => by
      simpa only [Pi.sub_apply] using hx)
  have hValueBound : ∀ n, ∀ᵐ x ∂μ,
      ‖(TauCeti.W1p.value (U n) - TauCeti.W1p.value U0) x‖ ^ 2 ≤
        4 * ‖TauCeti.W1p.value u x‖ ^ 2 := by
    intro n
    filter_upwards [hV n,hV0,hSubV n] with x hv hv0 hsub
    rw [hsub,hv,hv0]
    have hA : ‖max (TauCeti.W1p.value u x - κ n) 0‖ ≤ ‖TauCeti.W1p.value u x‖ := by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs]
      exact max_le_iff.mpr ⟨(sub_le_self _ (hκPos n).le).trans (le_abs_self _),abs_nonneg _⟩
    have hB : ‖max (TauCeti.W1p.value u x) 0‖ ≤ ‖TauCeti.W1p.value u x‖ := by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs]
      exact max_le_iff.mpr ⟨le_abs_self _,abs_nonneg _⟩
    have hd : ‖max (TauCeti.W1p.value u x - κ n) 0 - max (TauCeti.W1p.value u x) 0‖ ≤
        2 * ‖TauCeti.W1p.value u x‖ := by
      calc
        _ ≤ ‖max (TauCeti.W1p.value u x - κ n) 0‖ + ‖max (TauCeti.W1p.value u x) 0‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    nlinarith [hs]
  have hValuePointwise : ∀ᵐ x ∂μ,
      Tendsto (fun n => ‖(TauCeti.W1p.value (U n) - TauCeti.W1p.value U0) x‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr hV,hV0,ae_all_iff.mpr hSubV] with x hv hv0 hsub
    have hm : Tendsto (fun n => max (TauCeti.W1p.value u x - κ n) 0) atTop
        (𝓝 (max (TauCeti.W1p.value u x) 0)) := by
      simpa only [Pi.sub_apply,sub_zero] using (tendsto_const_nhds.sub hκ).max tendsto_const_nhds
    have hd : Tendsto (fun n => max (TauCeti.W1p.value u x - κ n) 0 - max (TauCeti.W1p.value u x) 0)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [Pi.sub_apply,sub_self] using hm.sub_const (max (TauCeti.W1p.value u x) 0)
    have he : ∀ n, ‖(TauCeti.W1p.value (U n) - TauCeti.W1p.value U0) x‖ ^ 2 =
        ‖max (TauCeti.W1p.value u x - κ n) 0 - max (TauCeti.W1p.value u x) 0‖ ^ 2 := by
      intro n
      rw [hsub n,hv n,hv0]
    have hn : Tendsto (fun n =>
        ‖max (TauCeti.W1p.value u x - κ n) 0 - max (TauCeti.W1p.value u x) 0‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def,Pi.pow_apply,norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hd.norm.pow 2
    exact hn.congr' (Eventually.of_forall (fun n => (he n).symm))
  have hValueLimit : Tendsto (fun n => TauCeti.W1p.value (U n)) atTop
      (𝓝 (TauCeti.W1p.value U0)) :=
    tendsto_Lp_two_of_dominated_squared_difference μ _ _ _
      (((Lp.memLp (TauCeti.W1p.value u)).integrable_norm_pow (by norm_num)).const_mul 4)
      hValueBound hValuePointwise
  exact hValueLimit

theorem tendsto_nativeH1_posPartAbove_gradient_one_div_add (u : BallH1) :
    Tendsto (fun n : ℕ => TauCeti.W1p.gradient (TauCeti.W1p.posPartAbove
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity) u)) atTop
      (𝓝 (TauCeti.W1p.gradient (TauCeti.W1p.posPart (by norm_num : (2 : ℝ≥0∞) ≠ ∞) u))) := by
  let μ : Measure R3 := (volume : Measure R3).restrict ballOpens
  let hp : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  let κ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hκPos : ∀ n, 0 < κ n := fun n => by dsimp only [κ]; positivity
  have hκ : Tendsto κ atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  let U : ℕ → BallH1 := fun n => TauCeti.W1p.posPartAbove hp (hκPos n).le u
  let U0 : BallH1 := TauCeti.W1p.posPart hp u
  have hG : ∀ n, TauCeti.W1p.gradient (U n) =ᵐ[μ]
      (fun x => if κ n < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else 0) :=
    fun n => nativeH1_gradient_posPartAbove_literal_ae u (κ n) (hκPos n).le
  have hG0 : TauCeti.W1p.gradient U0 =ᵐ[μ]
      (fun x => if 0 < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else 0) :=
    nativeH1_gradient_posPart_literal_ae u
  have hSubG : ∀ n, ⇑(TauCeti.W1p.gradient (U n) - TauCeti.W1p.gradient U0) =ᵐ[μ]
      (fun x => TauCeti.W1p.gradient (U n) x - TauCeti.W1p.gradient U0 x) :=
    fun n => (Lp.coeFn_sub _ _).mono (fun x hx => by
      simpa only [Pi.sub_apply] using hx)
  have hGradientBound : ∀ n, ∀ᵐ x ∂μ,
      ‖(TauCeti.W1p.gradient (U n) - TauCeti.W1p.gradient U0) x‖ ^ 2 ≤
        4 * ‖TauCeti.W1p.gradient u x‖ ^ 2 := by
    intro n
    filter_upwards [hG n,hG0,hSubG n] with x hg hg0 hsub
    rw [hsub,hg,hg0]
    by_cases ha : κ n < TauCeti.W1p.value u x <;>
      by_cases hb : 0 < TauCeti.W1p.value u x <;>
      simp only [ha,hb,ite_true,ite_false,sub_self,sub_zero,zero_sub,norm_zero,norm_neg,zero_pow] <;>
      nlinarith [sq_nonneg ‖TauCeti.W1p.gradient u x‖]
  have hGradientPointwise : ∀ᵐ x ∂μ,
      Tendsto (fun n => ‖(TauCeti.W1p.gradient (U n) - TauCeti.W1p.gradient U0) x‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr hG,hG0,ae_all_iff.mpr hSubG] with x hg hg0 hsub
    have hLiteral := tendsto_threshold_indicator_squared_difference (V := R3)
      κ hκPos hκ (TauCeti.W1p.value u x) (TauCeti.W1p.gradient u x)
    have hFun : (fun n : ℕ =>
        ‖(TauCeti.W1p.gradient (U n) - TauCeti.W1p.gradient U0) x‖ ^ 2) =
        (fun n : ℕ => ‖(if κ n < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else (0 : R3)) -
          (if 0 < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else (0 : R3))‖ ^ 2) := by
      funext n
      change ‖(TauCeti.W1p.gradient (U n) - TauCeti.W1p.gradient U0) x‖ ^ 2 =
        ‖(if κ n < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else (0 : R3)) -
          (if 0 < TauCeti.W1p.value u x then TauCeti.W1p.gradient u x else (0 : R3))‖ ^ 2
      rw [hsub n,hg n,hg0]
    exact Eq.mp (congrArg (fun F : ℕ → ℝ => Tendsto F atTop (𝓝 (0 : ℝ))) hFun.symm) hLiteral
  have hGradientLimit : Tendsto (fun n => TauCeti.W1p.gradient (U n)) atTop
      (𝓝 (TauCeti.W1p.gradient U0)) :=
    tendsto_Lp_two_of_dominated_squared_difference μ _ _ _
      (((Lp.memLp (TauCeti.W1p.gradient u)).integrable_norm_pow (by norm_num)).const_mul 4)
      hGradientBound hGradientPointwise
  exact hGradientLimit

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tendsto_nativeH1_posPartAbove_value_one_div_add
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tendsto_nativeH1_posPartAbove_gradient_one_div_add
