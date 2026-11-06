import Calderon.ActualMetricWronskianDivergence
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricVolume MetricOperator

theorem contDiff_neg_coordinateFluxDivergence_matrixGradient
    (a : MatrixField) (ha : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => a x i j))
    (φ : R3 → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun x : R3 => -coordinateFluxDivergence
      (fun z => matrixOperatorMap (a z) (gradient φ z)) x) := by
  have hJ (i : Fin 3) : ContDiff ℝ ∞
      (fun x => matrixOperatorMap (a x) (gradient φ x) i) := by
    have hD (j : Fin 3) : ContDiff ℝ ∞
        (fun x => fderiv ℝ φ x (MetricVolume.coordinateVector j)) :=
      (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    simp only [matrixOperator_coordinate, gradient_coordinate]
    exact ContDiff.sum (fun j _ => (ha i j).mul (hD j))
  apply ContDiff.neg
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3, fderiv ℝ
    (fun z => matrixOperatorMap (a z) (gradient φ z) i) x
    (NormalCoordinatesFrame.coordinateVector i))
  exact ContDiff.sum (fun i _ =>
    ((hJ i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem hasCompactSupport_neg_coordinateFluxDivergence_matrixGradient
    (a : MatrixField) (φ : R3 → ℝ) (hCompact : HasCompactSupport φ) :
    HasCompactSupport (fun x : R3 => -coordinateFluxDivergence
      (fun z => matrixOperatorMap (a z) (gradient φ z)) x) := by
  have hD (j : Fin 3) : HasCompactSupport
      (fun x => fderiv ℝ φ x (MetricVolume.coordinateVector j)) :=
    (hCompact.fderiv ℝ).comp_left
      (g := fun L : R3 →L[ℝ] ℝ => L (MetricVolume.coordinateVector j)) rfl
  have hJ (i : Fin 3) : HasCompactSupport
      (fun x => matrixOperatorMap (a x) (gradient φ x) i) := by
    let F : Fin 3 → R3 → ℝ := fun j x => a x i j * fderiv ℝ φ x (MetricVolume.coordinateVector j)
    have hF (j : Fin 3) : HasCompactSupport (F j) := (hD j).mul_left
    have hSum : HasCompactSupport (∑ j : Fin 3, F j) :=
      HasCompactSupport.finset_sum (s := Finset.univ) (f := F) (fun j _ => hF j)
    have hEq : (∑ j : Fin 3, F j) =
        (fun x => matrixOperatorMap (a x) (gradient φ x) i) := by
      funext x
      rw [Finset.sum_apply]
      simp only [matrixOperator_coordinate,gradient_coordinate,F]
    exact hEq ▸ hSum
  let D : Fin 3 → R3 → ℝ := fun i x => fderiv ℝ
    (fun z => matrixOperatorMap (a z) (gradient φ z) i) x (NormalCoordinatesFrame.coordinateVector i)
  have hDc (i : Fin 3) : HasCompactSupport (D i) :=
    ((hJ i).fderiv ℝ).comp_left
      (g := fun L : R3 →L[ℝ] ℝ => L (NormalCoordinatesFrame.coordinateVector i)) rfl
  have hSum : HasCompactSupport (∑ i : Fin 3, D i) :=
    HasCompactSupport.finset_sum (s := Finset.univ) (f := D) (fun i _ => hDc i)
  have hEq : (∑ i : Fin 3, D i) =
      (fun x : R3 => coordinateFluxDivergence (fun z => matrixOperatorMap (a z) (gradient φ z)) x) := by
    funext x
    exact Finset.sum_apply x Finset.univ D
  exact (hEq ▸ hSum).neg

end OAI.AnisotropicCalderon.ConnectionError
