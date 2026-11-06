import Calderon.NativeH2ConormalTraceRepresentative
import Calderon.NativeH2OrthogonalCoordinateTrace
import Calderon.NativeOrthogonalCoefficientEnergyCovariance

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic OrthogonalSphereMeasure ConnectionError MetricOperator

lemma coefficientFlux_sum_eq_matrixBilinearForm
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x v : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3, x i * A i j * v j) =
      TauCeti.PDE.matrixBilinearForm A x v := by
  simp only [TauCeti.PDE.matrixBilinearForm_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]

lemma coefficientFlux_orthogonal_covariance
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (x v : R3) :
    (∑ i : Fin 3, ∑ j : Fin 3, x i * orthogonalPrincipalCoefficient e a x i j * (e.symm v) j) =
      ∑ i : Fin 3, ∑ j : Fin 3, (e x) i * a (e x) i j * v j := by
  rw [coefficientFlux_sum_eq_matrixBilinearForm,coefficientFlux_sum_eq_matrixBilinearForm,
    matrixBilinearForm_eq_matrixOperator_inner,matrixBilinearForm_eq_matrixOperator_inner]
  have hMap : matrixOperatorMap (orthogonalPrincipalCoefficient e a x) (e.symm v) =
      e.symm (matrixOperatorMap (a (e x)) v) := by
    change (operatorMatrixMap _).toEuclideanLin (e.symm v) = _
    rw [operatorMatrixMap_apply]
    change e.symm (matrixOperatorMap (a (e x)) (e (e.symm v))) = _
    rw [e.apply_symm_apply]
  rw [hMap]
  simpa only [e.symm_apply_apply] using e.symm.inner_map_map (matrixOperatorMap (a (e x)) v) (e x)

lemma ordinaryConormalTraceL_nativeH2OrthogonalPullback
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (F G : SmoothCoefficientMatrix 2)
    (hFG : coefficientMatrixField 2 G = orthogonalPrincipalCoefficient e (coefficientMatrixField 2 F))
    (U : BallSobolev 2) :
    ordinaryConormalTraceL hcalc τ0 G (nativeH2OrthogonalPullback hcalc e U) =
      sphereL2OrthogonalPullback e (ordinaryConormalTraceL hcalc τ0 F U) := by
  have hder : ∀ᵐ x : UnitSphere ∂sphereProbability, ∀ j : Fin 3,
      strongCoordinateTraceL hcalc τ0 j (nativeH2OrthogonalPullback hcalc e U) x =
        (e.symm (WithLp.toLp 2 (fun l : Fin 3 =>
          strongCoordinateTraceL hcalc τ0 l U (orthogonalSphereHomeomorph e x)))) j :=
    ae_all_iff.mpr (fun j => strongCoordinateTraceL_nativeH2OrthogonalPullback_value_ae hcalc τ0 e U j)
  have hright := (orthogonalSphereHomeomorph_sphereProbability_preserving e).quasiMeasurePreserving.ae_eq_comp
    (ordinaryConormalTraceL_value_ae hcalc τ0 F U)
  apply Lp.ext
  filter_upwards [ordinaryConormalTraceL_value_ae hcalc τ0 G (nativeH2OrthogonalPullback hcalc e U),
    hder,Lp.coeFn_compMeasurePreserving (ordinaryConormalTraceL hcalc τ0 F U)
      (orthogonalSphereHomeomorph_sphereProbability_preserving e),hright] with x hL hd hR hr
  change _ = (Lp.compMeasurePreserving (orthogonalSphereHomeomorph e)
    (orthogonalSphereHomeomorph_sphereProbability_preserving e)
    (ordinaryConormalTraceL hcalc τ0 F U)) x
  rw [hL,hR,hr]
  simp_rw [hd]
  rw [hFG]
  exact coefficientFlux_orthogonal_covariance e (coefficientMatrixField 2 F) x.val
    (WithLp.toLp 2 (fun l : Fin 3 => strongCoordinateTraceL hcalc τ0 l U (orthogonalSphereHomeomorph e x)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientFlux_sum_eq_matrixBilinearForm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientFlux_orthogonal_covariance
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryConormalTraceL_nativeH2OrthogonalPullback
