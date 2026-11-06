import Calderon.NativeH2OrthogonalPullbackExistence
import Calderon.NativeH1OrthogonalValueTrace
import Calderon.NativeCoordinateTraceVariation

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic OrthogonalSphereMeasure

lemma strongCoordinateTraceL_nativeH2OrthogonalPullback
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) (j : Fin 3) :
    strongCoordinateTraceL hcalc τ0 j (nativeH2OrthogonalPullback hcalc e U) =
      ∑ l : Fin 3, (e (EuclideanSpace.single j 1)) l •
        sphereL2OrthogonalPullback e (strongCoordinateTraceL hcalc τ0 l U) := by
  rw [strongCoordinateTraceL_apply,coordinateDerivative_nativeH2OrthogonalPullback,
    nativeH2OrthogonalDerivativeComponent,map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [map_smul,valueTraceL_nativeH1OrthogonalPullback,strongCoordinateTraceL_apply]

lemma sphereL2_sum_smul_orthogonal_value_ae
    (e : R3 ≃ₗᵢ[ℝ] R3) (c : Fin 3 → ℝ) (v : Fin 3 → SphereL2) :
    (∑ l : Fin 3, c l • sphereL2OrthogonalPullback e (v l))
      =ᵐ[sphereProbability] fun x : UnitSphere =>
        ∑ l : Fin 3, c l * v l (orthogonalSphereHomeomorph e x) := by
  have ht (l : Fin 3) : c l • sphereL2OrthogonalPullback e (v l)
      =ᵐ[sphereProbability] fun x : UnitSphere => c l * v l (orthogonalSphereHomeomorph e x) := by
    filter_upwards [Lp.coeFn_smul (c l) (sphereL2OrthogonalPullback e (v l)),
      Lp.coeFn_compMeasurePreserving (v l)
        (orthogonalSphereHomeomorph_sphereProbability_preserving e)] with x hs hr
    exact hs.trans (congrArg (c l * ·) hr)
  exact (Lp.coeFn_finsetSum Finset.univ _).trans (eventuallyEq_sum fun l _ => ht l)

lemma strongCoordinateTraceL_nativeH2OrthogonalPullback_value_ae
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (U : BallSobolev 2) (j : Fin 3) :
    strongCoordinateTraceL hcalc τ0 j (nativeH2OrthogonalPullback hcalc e U)
      =ᵐ[sphereProbability] fun x : UnitSphere =>
        (e.symm (WithLp.toLp 2 (fun l : Fin 3 =>
          strongCoordinateTraceL hcalc τ0 l U (orthogonalSphereHomeomorph e x)))) j := by
  rw [strongCoordinateTraceL_nativeH2OrthogonalPullback]
  have h := sphereL2_sum_smul_orthogonal_value_ae e
    (fun l => (e (EuclideanSpace.single j 1)) l) (fun l => strongCoordinateTraceL hcalc τ0 l U)
  exact h.trans (ae_of_all sphereProbability fun x =>
    (orthogonal_inverse_coordinate_eq_sum e j
      (WithLp.toLp 2 (fun l : Fin 3 =>
        strongCoordinateTraceL hcalc τ0 l U (orthogonalSphereHomeomorph e x)))).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.strongCoordinateTraceL_nativeH2OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereL2_sum_smul_orthogonal_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.strongCoordinateTraceL_nativeH2OrthogonalPullback_value_ae
