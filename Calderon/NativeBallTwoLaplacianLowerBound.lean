import Calderon.RadiusTwoNativeSourceFoundation

/-! EXPANSION.json precedes the derived actual native graph-norm lower estimate. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma native_laplacian_lower_bound_of_subset_ball_two (U : Opens R3)
    (hU : (U : Set R3) ⊆ ball (0 : R3) 2) (w : W1p0 (volume : Measure R3) U 2) :
    (1/34 : ℝ) * ‖w‖ ^ 2 ≤
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (w : W1p (volume : Measure R3) U 2) (w : W1p (volume : Measure R3) U 2) := by
  have hn : ‖(w : W1p (volume : Measure R3) U 2)‖ = ‖w‖ := rfl
  have hb := (uniformlyEllipticOn_const_one_one (U : Set R3)).mul_norm_sq_le_energyFormH1_self_of_subset_ball
    aestronglyMeasurable_const aestronglyMeasurable_const aestronglyMeasurable_const
    (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) (beta := 0) (gamma := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (z := 0) (R := 2) hU w.2
  rw [hn] at hb
  norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul,sub_zero,mul_one] at hb
  exact hb

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_laplacian_lower_bound_of_subset_ball_two
