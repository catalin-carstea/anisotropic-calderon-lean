import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.OrderClosed

/-! EXPANSION.json precedes ordinary vector threshold-indicator squared-difference convergence. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace OAI.AnisotropicCalderon.EnergyBridge

theorem tendsto_threshold_indicator_squared_difference
    {V : Type*} [NormedAddCommGroup V] (κ : ℕ → ℝ)
    (hκPos : ∀ n, 0 < κ n) (hκ : Tendsto κ atTop (𝓝 (0 : ℝ))) (t : ℝ) (v : V) :
    Tendsto (fun n => ‖(if κ n < t then v else (0 : V)) -
      (if 0 < t then v else (0 : V))‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
  let F : ℕ → ℝ := fun n => ‖(if κ n < t then v else (0 : V)) -
    (if 0 < t then v else (0 : V))‖ ^ 2
  have hEq : F =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
    by_cases ht : 0 < t
    · have hSmall : ∀ᶠ n in atTop, κ n < t := hκ.eventually (Iio_mem_nhds ht)
      exact hSmall.mono (fun n hn => by
        change ‖(if κ n < t then v else (0 : V)) - (if 0 < t then v else (0 : V))‖ ^ 2 = (0 : ℝ)
        rw [if_pos hn,if_pos ht,sub_self,norm_zero]
        norm_num)
    · exact Eventually.of_forall (fun n => by
        have hn : ¬ κ n < t := fun hn => ht (lt_trans (hκPos n) hn)
        change ‖(if κ n < t then v else (0 : V)) - (if 0 < t then v else (0 : V))‖ ^ 2 = (0 : ℝ)
        rw [if_neg hn,if_neg ht,sub_self,norm_zero]
        norm_num)
  have hConst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds
  exact hConst.congr' hEq.symm

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tendsto_threshold_indicator_squared_difference
