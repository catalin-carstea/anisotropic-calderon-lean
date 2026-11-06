import Calderon.NativeSupportedDriftDivergenceOrthogonalCovariance
import Calderon.NativeOrthogonalCoefficientEnergyCovariance

set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator

lemma orthogonalPrincipalCoefficient_transpose
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) :
    orthogonalPrincipalCoefficient e (fun x => (a x)ᵀ) =
      (fun x => (orthogonalPrincipalCoefficient e a x)ᵀ) := by
  funext x
  rw [orthogonalPrincipalCoefficient_eq_matrix_conjugation,
    orthogonalPrincipalCoefficient_eq_matrix_conjugation]
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]

lemma orthogonalDriftCoefficient_neg (e : R3 ≃ₗᵢ[ℝ] R3) (beta : R3 → R3) :
    orthogonalDriftCoefficient e (-beta) = -(orthogonalDriftCoefficient e beta) := by
  funext x
  change e.symm (-(beta (e x))) = -(e.symm (beta (e x)))
  exact e.symm.map_neg _

lemma formalAdjointMass_orthogonalDriftCoefficient
    (e : R3 ≃ₗᵢ[ℝ] R3) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (c : R3 → ℝ) :
    (fun x => c (e x)-nativeSupportedDriftDivergence (orthogonalDriftCoefficient e beta) x) =
      (fun x => c x-nativeSupportedDriftDivergence beta x) ∘ e := by
  funext x
  exact congrArg (fun d : ℝ => c (e x)-d)
    (nativeSupportedDriftDivergence_orthogonalDriftCoefficient e beta hbeta x)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonalPrincipalCoefficient_transpose
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.orthogonalDriftCoefficient_neg
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.formalAdjointMass_orthogonalDriftCoefficient
