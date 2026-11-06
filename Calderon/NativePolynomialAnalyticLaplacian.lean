import Calderon.GreenEuclidean
import Calderon.SmoothAngularCasimir
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open SmoothAngularCasimir

lemma analyticLaplacian_eq_euclideanLaplacian (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    Laplacian.laplacian f x = euclideanLaplacian f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_two_apply]
  simp only [EuclideanSpace.basisFun_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  change fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
    fderiv ℝ (fun y : R3 => fderiv ℝ f y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp) x
  rw [fderiv_clm_apply hdf (differentiableAt_const (EuclideanSpace.single i (1 : ℝ)))]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]

lemma analyticLaplacian_polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) :
    Laplacian.laplacian (polynomialEvaluation p) =
      polynomialEvaluation (AngularPolynomial.laplacian p) := by
  funext x
  rw [analyticLaplacian_eq_euclideanLaplacian _ (contDiff_polynomialEvaluation p),
    euclideanLaplacian_polynomialEvaluation]

end OAI.AnisotropicCalderon.GreenRadialTrace

#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.analyticLaplacian_eq_euclideanLaplacian
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.analyticLaplacian_polynomialEvaluation
