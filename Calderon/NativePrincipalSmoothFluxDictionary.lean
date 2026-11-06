import Calderon.NativeSmoothOperatorRealization
import Calderon.ActualMetricWronskianDivergence
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap

theorem coordinateFluxDivergence_matrixGradient_eq_double_sum
    (a : MatrixField) (ha : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun x => a x i j))
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (z : R3) :
    coordinateFluxDivergence (fun x => matrixOperatorMap (a x) (gradient f x)) z =
      ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ
        (fun x => a x i j * fderiv ℝ f x (MetricVolume.coordinateVector j)) z
          (MetricVolume.coordinateVector i) := by
  have hD (j : Fin 3) : ContDiff ℝ ∞ (fun x => fderiv ℝ f x (MetricVolume.coordinateVector j)) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hRow (i : Fin 3) :
      (fun x => matrixOperatorMap (a x) (gradient f x) i) =
        (fun x => ∑ j : Fin 3, a x i j * fderiv ℝ f x (MetricVolume.coordinateVector j)) := by
    funext x
    simp only [matrixOperator_coordinate,gradient_coordinate]
  have hCoord (i : Fin 3) : NormalCoordinatesFrame.coordinateVector i = MetricVolume.coordinateVector i := by
    ext j
    simp [NormalCoordinatesFrame.coordinateVector,MetricVolume.coordinateVector]
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  rw [hRow,hCoord]
  let T : Fin 3 → R3 → ℝ := fun j x => a x i j * fderiv ℝ f x (MetricVolume.coordinateVector j)
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin 3)), DifferentiableAt ℝ (T j) z :=
    fun j _ => ((ha i j).mul (hD j)).differentiable (by simp) z
  have hSum : fderiv ℝ (fun x => ∑ j : Fin 3, T j x) z = ∑ j : Fin 3, fderiv ℝ (T j) z :=
    fderiv_fun_sum hd
  rw [hSum]
  simp only [sum_apply,T]

theorem ordinaryPrincipalL_smoothBallSobolev_value_ae_coordinateFlux
    (hcalc : FixedSobolevCalculus) (s : ℕ) (F : SmoothCoefficientMatrix (s+2))
    (f : SmoothData) :
    TauCeti.Wkp.value s (ordinaryPrincipalL hcalc s F (smoothBallSobolev (s+2) f))
      =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => -coordinateFluxDivergence
        (fun z => matrixOperatorMap (coefficientMatrixField (s+2) F z) (gradient f.1 z)) x) := by
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun x => coefficientMatrixField (s+2) F x i j) :=
    contDiff_coefficientValue (s+2) (F i j)
  filter_upwards [ordinaryPrincipalL_smoothBallSobolev_value_ae hcalc s F f] with x hx
  rw [hx,coordinateFluxDivergence_matrixGradient_eq_double_sum _ ha f.1 f.2]
  rfl

theorem coordinateFluxDivergence_matrixGradient_congr_of_eventuallyEq
    (a : MatrixField) (f g : R3 → ℝ) (z : R3) (h : f =ᶠ[𝓝 z] g) :
    coordinateFluxDivergence (fun x => matrixOperatorMap (a x) (gradient f x)) z =
      coordinateFluxDivergence (fun x => matrixOperatorMap (a x) (gradient g x)) z := by
  have hGrad : gradient f =ᶠ[𝓝 z] gradient g := h.gradient
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hRow : (fun x => matrixOperatorMap (a x) (gradient f x) i) =ᶠ[𝓝 z]
      (fun x => matrixOperatorMap (a x) (gradient g x) i) :=
    hGrad.mono (fun x hx => congrArg (fun v : R3 => matrixOperatorMap (a x) v i) hx)
  rw [hRow.fderiv_eq (𝕜 := ℝ)]

theorem tsupport_neg_coordinateFluxDivergence_matrixGradient_subset
    (a : MatrixField) (f : R3 → ℝ) :
    tsupport (fun z => -coordinateFluxDivergence (fun x => matrixOperatorMap (a x) (gradient f x)) z) ⊆
      tsupport f := by
  change closure (Function.support _) ⊆ tsupport f
  apply closure_minimal _ (isClosed_tsupport f)
  intro z hz
  by_contra hNot
  have hNear : f =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [((isClosed_tsupport f).isOpen_compl.mem_nhds hNot)] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hEq := coordinateFluxDivergence_matrixGradient_congr_of_eventuallyEq a f (fun _ => 0) z hNear
  have hZero : coordinateFluxDivergence (fun x => matrixOperatorMap (a x) (gradient f x)) z = 0 := by
    rw [hEq]
    simp [coordinateFluxDivergence]
  apply hz
  change -coordinateFluxDivergence (fun x => matrixOperatorMap (a x) (gradient f x)) z = 0
  rw [hZero,neg_zero]

end OAI.AnisotropicCalderon.ConnectionError
