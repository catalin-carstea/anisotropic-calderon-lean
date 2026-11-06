import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option maxSynthPendingDepth 10
noncomputable section
open ContinuousLinearMap MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

section GeneralAssembly
variable {I X W H : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Select the fixed matrix entry before composing its operator. -/
def operatorMatrixEntryL (i j : I) :
    (I → I → W →L[ℝ] W) →L[ℝ] W →L[ℝ] W :=
  (ContinuousLinearMap.proj j : (I → W →L[ℝ] W) →L[ℝ] W →L[ℝ] W).comp
    (ContinuousLinearMap.proj i : (I → I → W →L[ℝ] W) →L[ℝ] I → W →L[ℝ] W)

/-- Minus the coordinate sum of actual derivative/multiplier/derivative compositions. -/
def coefficientDivergenceL (D : I → W →L[ℝ] H) (R : I → X →L[ℝ] W) :
    (I → I → W →L[ℝ] W) →L[ℝ] X →L[ℝ] H :=
  -∑ i, ∑ j,
    ((ContinuousLinearMap.compL ℝ X W H).flip (R j)).comp
      ((ContinuousLinearMap.compL ℝ W W H (D i)).comp
        (operatorMatrixEntryL i j))

theorem coefficientDivergenceL_apply (D : I → W →L[ℝ] H) (R : I → X →L[ℝ] W)
    (A : I → I → W →L[ℝ] W) :
    coefficientDivergenceL D R A = -∑ i, ∑ j, ((D i).comp (A i j)).comp (R j) := by
  simp [coefficientDivergenceL, operatorMatrixEntryL]

theorem coefficientDivergenceL_apply_apply (D : I → W →L[ℝ] H)
    (R : I → X →L[ℝ] W) (A : I → I → W →L[ℝ] W) (u : X) :
    coefficientDivergenceL D R A u = -∑ i, ∑ j, D i (A i j (R j u)) := by
  simp [coefficientDivergenceL_apply]

theorem norm_coefficientDivergenceL_apply_le (D : I → W →L[ℝ] H)
    (R : I → X →L[ℝ] W) (A : I → I → W →L[ℝ] W) :
    ‖coefficientDivergenceL D R A‖ ≤ ∑ i, ∑ j, ‖D i‖ * ‖A i j‖ * ‖R j‖ := by
  rw [coefficientDivergenceL_apply, norm_neg]
  calc
    ‖∑ i, ∑ j, ((D i).comp (A i j)).comp (R j)‖
        ≤ ∑ i, ‖∑ j, ((D i).comp (A i j)).comp (R j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖((D i).comp (A i j)).comp (R j)‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖D i‖ * ‖A i j‖ * ‖R j‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
end GeneralAssembly


end OAI.AnisotropicCalderon.DirichletFamily
