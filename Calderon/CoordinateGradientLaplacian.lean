import Calderon.ConformalFluxDivergence
import Calderon.MetricHessianDivergence
import Mathlib.Analysis.InnerProductSpace.Laplacian
set_option autoImplicit false
noncomputable section
open scoped ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError

theorem coordinateFluxDivergence_gradient_eq_laplacian
    (f : R3 → ℝ) (x : R3) (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    coordinateFluxDivergence (gradient f) x = Laplacian.laplacian f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  unfold coordinateFluxDivergence
  simp_rw [MetricVolume.gradient_coordinate,iteratedFDeriv_two_apply]
  apply Finset.sum_congr rfl
  intro i _
  simpa [NormalCoordinatesFrame.coordinateVector,MetricVolume.coordinateVector,
    EuclideanSpace.basisFun_apply] using
    MetricVolume.derivative_covector_entry f x (MetricVolume.coordinateVector i) hf i

theorem coordinateFluxDivergence_gradient_eq_laplacian_of_contDiff
    (f : R3 → ℝ) (hf : ContDiff ℝ 2 f) (x : R3) :
    coordinateFluxDivergence (gradient f) x = Laplacian.laplacian f x := by
  apply coordinateFluxDivergence_gradient_eq_laplacian f x
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x

end OAI.AnisotropicCalderon.ConnectionError
