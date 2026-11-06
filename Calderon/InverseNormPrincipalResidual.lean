import Calderon.InverseNormPotentialCalderon
import Calderon.ActualMetricWronskianDivergence
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume

theorem coordinateFluxDivergence_matrix_gradient_inverseNormPotential
    (a : MatrixField) (c0 : ℝ) (z : R3) (hz : z ≠ 0)
    (ha : ∀ i j : Fin 3, DifferentiableAt ℝ (fun x => a x i j) z) :
    -coordinateFluxDivergence
      (fun x => matrixOperatorMap (a x) (gradient (inverseNormPotential c0) x)) z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) *
          (c0 / ‖z‖^3 * z j) +
         a z i j * (c0 / ‖z‖^3 * (if j = i then 1 else 0) -
           3*c0 / ‖z‖^5 * z i * z j)) := by
  have hHess := hasFDerivAt_gradient_inverseNormPotential c0 z hz
  have hGrad (j : Fin 3) : DifferentiableAt ℝ
      (fun x => gradient (inverseNormPotential c0) x j) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp z hHess).differentiableAt
  have hRow (i : Fin 3) :
      fderiv ℝ (fun x => matrixOperatorMap (a x) (gradient (inverseNormPotential c0) x) i) z
        (NormalCoordinatesFrame.coordinateVector i) =
        ∑ j : Fin 3,
          (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) *
            gradient (inverseNormPotential c0) z j +
           a z i j * fderiv ℝ (fun x => gradient (inverseNormPotential c0) x j) z
             (NormalCoordinatesFrame.coordinateVector i)) := by
    let F : Fin 3 → R3 → ℝ := fun j x => a x i j * gradient (inverseNormPotential c0) x j
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin 3)), DifferentiableAt ℝ (F j) z :=
      fun j _ => (ha i j).mul (hGrad j)
    have hs : fderiv ℝ (fun x => ∑ j : Fin 3, F j x) z =
        ∑ j : Fin 3, fderiv ℝ (F j) z := fderiv_fun_sum hd
    simp only [matrixOperator_coordinate]
    change (fderiv ℝ (fun x => ∑ j : Fin 3, F j x) z)
      (NormalCoordinatesFrame.coordinateVector i) = _
    rw [hs]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hm := (ha i j).hasFDerivAt.mul (hGrad j).hasFDerivAt
    have he := congrArg (fun D : R3 →L[ℝ] ℝ => D (NormalCoordinatesFrame.coordinateVector i)) hm.fderiv
    change (fderiv ℝ (F j) z) (NormalCoordinatesFrame.coordinateVector i) = _ at he
    rw [he]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hEntry (i j : Fin 3) :
      fderiv ℝ (fun x => gradient (inverseNormPotential c0) x j) z
        (NormalCoordinatesFrame.coordinateVector i) =
        3*c0 / ‖z‖^5 * z i * z j -
          c0 / ‖z‖^3 * (if j = i then 1 else 0) := by
    have hp := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp z hHess
    change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) j) ∘ gradient (inverseNormPotential c0)) z
      (NormalCoordinatesFrame.coordinateVector i) = _
    rw [hp.fderiv]
    simp [ContinuousLinearMap.comp_apply, NormalCoordinatesFrame.coordinateVector,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right]
    ring
  unfold coordinateFluxDivergence
  simp_rw [hRow]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hEntry, gradient_inverseNormPotential c0 z hz]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem coordinateFluxDivergence_matrix_gradient_inverseNormPotential_sub_one
    (a : MatrixField) (c0 : ℝ) (z : R3) (hz : z ≠ 0)
    (ha : ∀ i j : Fin 3, DifferentiableAt ℝ (fun x => a x i j) z) :
    -coordinateFluxDivergence
      (fun x => matrixOperatorMap (a x) (gradient (inverseNormPotential c0) x)) z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) *
          (c0 / ‖z‖^3 * z j) +
         (a z i j - (if i = j then 1 else 0)) *
          (c0 / ‖z‖^3 * (if j = i then 1 else 0) -
           3*c0 / ‖z‖^5 * z i * z j)) := by
  have hOne : (fun x : R3 => matrixOperatorMap (1 : Matrix (Fin 3) (Fin 3) ℝ)
      (gradient (inverseNormPotential c0) x)) = gradient (inverseNormPotential c0) := by
    funext x
    ext i
    simp [matrixOperator_coordinate, Matrix.one_apply]
  have hId := coordinateFluxDivergence_matrix_gradient_inverseNormPotential
    (fun _ => 1) c0 z hz (fun _ _ => differentiableAt_const _)
  rw [hOne,coordinateFluxDivergence_gradient_inverseNormPotential c0 z hz] at hId
  simp only [neg_zero,fderiv_const_apply,zero_apply,zero_mul,zero_add,Matrix.one_apply] at hId
  rw [coordinateFluxDivergence_matrix_gradient_inverseNormPotential a c0 z hz ha]
  let Q : Fin 3 → Fin 3 → ℝ := fun i j =>
    c0 / ‖z‖^3 * (if j = i then 1 else 0) - 3*c0 / ‖z‖^5*z i*z j
  have hZero : (∑ i : Fin 3, ∑ j : Fin 3, (if i=j then 1 else 0)*Q i j) = 0 := hId.symm
  have hRewrite :
      (∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) *
          (c0/‖z‖^3*z j) + a z i j*Q i j)) -
      (∑ i : Fin 3, ∑ j : Fin 3, (if i=j then 1 else 0)*Q i j) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) *
          (c0/‖z‖^3*z j) + (a z i j-(if i=j then 1 else 0))*Q i j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hZero,sub_zero] at hRewrite
  exact hRewrite

theorem coordinateFluxDivergence_matrix_gradient_inverseNormPotential_factorized
    (a : MatrixField) (c0 : ℝ) (z : R3) (hz : z ≠ 0)
    (ha : ∀ i j : Fin 3, DifferentiableAt ℝ (fun x => a x i j) z)
    (T : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (U : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hT : ∀ i j : Fin 3, a z i j - (if i = j then 1 else 0) =
      ∑ k : Fin 3, ∑ l : Fin 3, T i j k l * z k * z l)
    (hU : ∀ i j : Fin 3,
      fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i) =
        ∑ k : Fin 3, U i j k * z k) :
    -coordinateFluxDivergence
      (fun x => matrixOperatorMap (a x) (gradient (inverseNormPotential c0) x)) z =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        c0 * U i j k * (z k * z j / ‖z‖^3)) +
      (∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        c0 * T i i k l * (z k * z l / ‖z‖^3)) -
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        3*c0 * T i j k l * (z k * z l * z i * z j / ‖z‖^5)) := by
  let b : Fin 3 → Fin 3 → ℝ := fun i j => a z i j - (if i=j then 1 else 0)
  let d : Fin 3 → Fin 3 → ℝ := fun i j =>
    fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i)
  have hDiag : (∑ i : Fin 3, ∑ j : Fin 3,
      b i j * (c0/‖z‖^3*(if j=i then 1 else 0))) =
      ∑ i : Fin 3, b i i*(c0/‖z‖^3) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hBase :
      -coordinateFluxDivergence
        (fun x => matrixOperatorMap (a x) (gradient (inverseNormPotential c0) x)) z =
      (∑ i : Fin 3, ∑ j : Fin 3, d i j*(c0/‖z‖^3*z j)) +
      (∑ i : Fin 3, b i i*(c0/‖z‖^3)) -
      (∑ i : Fin 3, ∑ j : Fin 3, b i j*(3*c0/‖z‖^5*z i*z j)) := by
    rw [coordinateFluxDivergence_matrix_gradient_inverseNormPotential_sub_one a c0 z hz ha]
    change (∑ i : Fin 3, ∑ j : Fin 3,
      (d i j*(c0/‖z‖^3*z j)+b i j*(c0/‖z‖^3*(if j=i then 1 else 0)-3*c0/‖z‖^5*z i*z j))) = _
    simp only [mul_sub,← add_sub_assoc,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [hDiag]
  have hD : (∑ i : Fin 3, ∑ j : Fin 3, d i j*(c0/‖z‖^3*z j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, c0*U i j k*(z k*z j/‖z‖^3) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (fderiv ℝ (fun x => a x i j) z (NormalCoordinatesFrame.coordinateVector i))*(c0/‖z‖^3*z j) = _
    rw [hU]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hTdiag : (∑ i : Fin 3, b i i*(c0/‖z‖^3)) =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, c0*T i i k l*(z k*z l/‖z‖^3) := by
    apply Finset.sum_congr rfl
    intro i _
    change (a z i i-(if i=i then 1 else 0))*(c0/‖z‖^3) = _
    rw [hT]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hTquad : (∑ i : Fin 3, ∑ j : Fin 3, b i j*(3*c0/‖z‖^5*z i*z j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        3*c0*T i j k l*(z k*z l*z i*z j/‖z‖^5) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (a z i j-(if i=j then 1 else 0))*(3*c0/‖z‖^5*z i*z j) = _
    rw [hT]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hBase,hD,hTdiag,hTquad]

end OAI.AnisotropicCalderon.ConnectionError
