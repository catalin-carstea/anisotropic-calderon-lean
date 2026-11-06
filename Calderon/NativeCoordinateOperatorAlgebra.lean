import Calderon.SourceResponseEuclideanChart
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
open EnergyBridge MetricVolume

theorem sum_projection_smulRight_coordinateVector :
    (∑ i : Fin 3, (EuclideanSpace.proj i).smulRight (coordinateVector i)) =
      ContinuousLinearMap.id ℝ R3 := by
  apply ContinuousLinearMap.ext
  intro v
  ext k
  fin_cases k <;> simp [Fin.sum_univ_three, coordinateVector, PiLp.single_apply]

theorem sum_smulRight_sub
    {ι : Type*} [Fintype ι] (A B : ι → R3 →L[ℝ] ℝ) (v : ι → R3) :
    (∑ i, (A i).smulRight (v i)) - (∑ i, (B i).smulRight (v i)) =
      ∑ i, (A i - B i).smulRight (v i) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [_root_.sub_apply, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    ← Finset.sum_sub_distrib, sub_smul]

theorem norm_sum_smulRight_coordinateVector_le_sum
    (A : Fin 3 → R3 →L[ℝ] ℝ) :
    ‖∑ i : Fin 3, (A i).smulRight (coordinateVector i)‖ ≤ ∑ i : Fin 3, ‖A i‖ := by
  calc
    ‖∑ i : Fin 3, (A i).smulRight (coordinateVector i)‖ ≤
        ∑ i : Fin 3, ‖(A i).smulRight (coordinateVector i)‖ :=
      norm_sum_le (E := R3 →L[ℝ] R3) _ _
    _ = ∑ i : Fin 3, ‖A i‖ * ‖coordinateVector i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ContinuousLinearMap.norm_smulRight_apply (A i) (coordinateVector i)
    _ = ∑ i : Fin 3, ‖A i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [coordinateVector, EuclideanSpace.norm_single]

end OAI.AnisotropicCalderon.ExteriorSource.FixedSourceJetFrame
