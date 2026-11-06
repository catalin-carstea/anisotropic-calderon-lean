import Calderon.PrivateNewtonianDistributionalLaplacian
import Calderon.CoordinateGradientLaplacian
import Calderon.InverseNormPotentialCalderon
import Calderon.NativePolynomialBulkMoments
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError
open NativePolynomialBulkMoments

theorem inverseNormPotential_sphereSurfaceMass_eq_newtonianKernel (x : R3) :
    inverseNormPotential sphereSurfaceMass⁻¹ x = TauCeti.newtonianKernel 3 x := by
  rw [TauCeti.newtonianKernel_def,NativePolynomialBulkMoments.sphereSurfaceMass_eq_three_ballVolume]
  norm_num [inverseNormPotential,Real.rpow_neg_one,div_eq_mul_inv]

theorem integral_inverseNormPotential_mul_neg_coordinateFluxDivergence_gradient
    (φ : R3 → ℝ) (hφ : ContDiff ℝ 2 φ) (hCompact : HasCompactSupport φ) :
    (∫ x : R3, inverseNormPotential sphereSurfaceMass⁻¹ x *
      (-coordinateFluxDivergence (gradient φ) x)) = φ 0 := by
  have h := TauCeti.integral_laplacian_mul_newtonianKernel (n := 3) (by decide) hφ hCompact
  calc
    _ = -(∫ x : R3, Laplacian.laplacian φ x * TauCeti.newtonianKernel 3 x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change inverseNormPotential sphereSurfaceMass⁻¹ x *
          (-coordinateFluxDivergence (gradient φ) x) =
            -(Laplacian.laplacian φ x * TauCeti.newtonianKernel 3 x)
        rw [coordinateFluxDivergence_gradient_eq_laplacian_of_contDiff φ hφ x,
          inverseNormPotential_sphereSurfaceMass_eq_newtonianKernel]
        ring
    _ = _ := by rw [h];simp

theorem integral_inverseNormPotential_sub_mul_neg_coordinateFluxDivergence_gradient
    (φ : R3 → ℝ) (hφ : ContDiff ℝ 2 φ) (hCompact : HasCompactSupport φ) (a : R3) :
    (∫ x : R3, inverseNormPotential sphereSurfaceMass⁻¹ (x-a) *
      (-coordinateFluxDivergence (gradient φ) x)) = φ a := by
  have h := TauCeti.integral_laplacian_mul_newtonianKernel_sub (n := 3) (by decide) hφ hCompact a
  calc
    _ = -(∫ x : R3, Laplacian.laplacian φ x * TauCeti.newtonianKernel 3 (x-a)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change inverseNormPotential sphereSurfaceMass⁻¹ (x-a) *
          (-coordinateFluxDivergence (gradient φ) x) =
            -(Laplacian.laplacian φ x * TauCeti.newtonianKernel 3 (x-a))
        rw [coordinateFluxDivergence_gradient_eq_laplacian_of_contDiff φ hφ x,
          inverseNormPotential_sphereSurfaceMass_eq_newtonianKernel]
        ring
    _ = _ := by rw [h];simp

theorem hasWeakFDerivOn_inverseNormPotential_sphereSurfaceMass
    (V : TopologicalSpace.Opens R3) :
    TauCeti.HasWeakFDerivOn volume V (inverseNormPotential sphereSurfaceMass⁻¹)
      (fderiv ℝ (inverseNormPotential sphereSurfaceMass⁻¹)) := by
  have hEq : inverseNormPotential sphereSurfaceMass⁻¹ = TauCeti.newtonianKernel 3 :=
    funext inverseNormPotential_sphereSurfaceMass_eq_newtonianKernel
  rw [hEq]
  exact TauCeti.hasWeakFDerivOn_newtonianKernel (n := 3) (by decide) V

end OAI.AnisotropicCalderon.ConnectionError
