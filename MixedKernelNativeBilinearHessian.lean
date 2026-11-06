import MixedKernelNativeCommonPhaseBounds
import Calderon.MetricHessianQuadratic
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator MetricVolume
open scoped ContDiff Topology InnerProductSpace

/-- Genuine finite linearity extends coordinate bounds, with the unchanged Euclidean norm. -/
theorem abs_linear_map_le_of_coordinate_bounds
    (ell : R3 →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hCols : ∀ i : Fin 3, |ell (coordinateVector i)| ≤ C) (U : R3) :
    |ell U| ≤ (3*C)*‖U‖ := by
  have hSum : U=∑ i : Fin 3, U i • coordinateVector i := by
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr U]
    simp only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,coordinateVector]
  calc
    |ell U| = |∑ i : Fin 3, U i*ell (coordinateVector i)| := by
      conv_lhs => rw [hSum,map_sum]
      simp only [map_smul,smul_eq_mul]
    _ ≤ ∑ i : Fin 3, |U i*ell (coordinateVector i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ‖U‖*C := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le U i)
        (hCols i) (abs_nonneg _) (norm_nonneg U)
    _ = (3*C)*‖U‖ := by simp;ring

/-- Coordinate-pair estimates control the full genuine bilinear form. -/
theorem abs_bilinear_map_le_of_coordinate_bounds
    (B : R3 →L[ℝ] R3 →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hCols : ∀ i j : Fin 3, |B (coordinateVector i) (coordinateVector j)| ≤ C) (U V : R3) :
    |B U V| ≤ (9*C)*‖U‖*‖V‖ := by
  have hRows (j : Fin 3) : |B U (coordinateVector j)| ≤ (3*C)*‖U‖ :=
    abs_linear_map_le_of_coordinate_bounds (B.flip (coordinateVector j)) C hC (fun i => hCols i j) U
  have hh := abs_linear_map_le_of_coordinate_bounds (B U) ((3*C)*‖U‖) (by positivity) hRows V
  nlinarith only [hh]

/-- Extend BOTH actual common-phase Hessian column estimates to arbitrary native frame vectors. -/
theorem native_hessian_column_estimates_extend
    (rho : R3 × R3 → ℝ) (q : R3 × R3) (J F : R3 →L[ℝ] R3)
    (Gamma : R3 →L[ℝ] R3 →L[ℝ] R3) (r C : ℝ) (hC : 0 ≤ C)
    (hMixed : ∀ (i : Fin 3) (U : R3),
      |r^2*fderiv ℝ (fderiv ℝ rho) q (J U,0) (0,F (coordinateVector i))+
        ⟪U,coordinateVector i⟫_ℝ| ≤ C*r^2*‖U‖)
    (hYY : ∀ i j : Fin 3,
      |r^2*(fderiv ℝ (fderiv ℝ rho) q (0,F (coordinateVector i)) (0,F (coordinateVector j))-
        fderiv ℝ rho q (0,Gamma (F (coordinateVector i)) (F (coordinateVector j))))-
        ⟪coordinateVector i,coordinateVector j⟫_ℝ| ≤ C*r^2) :
    (∀ U V : R3, |r^2*fderiv ℝ (fderiv ℝ rho) q (J U,0) (0,F V)+⟪U,V⟫_ℝ| ≤
      (3*C)*r^2*‖U‖*‖V‖) ∧
    (∀ U V : R3, |r^2*(fderiv ℝ (fderiv ℝ rho) q (0,F U) (0,F V)-
      fderiv ℝ rho q (0,Gamma (F U) (F V)))-⟪U,V⟫_ℝ| ≤
      (9*C)*r^2*‖U‖*‖V‖) := by
  let K1 := (ContinuousLinearMap.inl ℝ R3 R3).comp J
  let K2 := (ContinuousLinearMap.inr ℝ R3 R3).comp F
  let H := fderiv ℝ (fderiv ℝ rho) q
  let ellY := (fderiv ℝ rho q).comp (ContinuousLinearMap.inr ℝ R3 R3)
  let I0 : R3 →L[ℝ] R3 →L[ℝ] ℝ := innerSL ℝ
  let Bmixed : R3 →L[ℝ] R3 →L[ℝ] ℝ := r^2 • H.bilinearComp K1 K2+I0
  let Byy : R3 →L[ℝ] R3 →L[ℝ] ℝ :=
    r^2 • (H.bilinearComp K2 K2-
      ((ContinuousLinearMap.compL ℝ R3 R3 ℝ) ellY).comp (Gamma.bilinearComp F F))-I0
  have hMixEval (U V : R3) : Bmixed U V=
      r^2*fderiv ℝ (fderiv ℝ rho) q (J U,0) (0,F V)+⟪U,V⟫_ℝ := rfl
  have hYYEval (U V : R3) : Byy U V=
      r^2*(fderiv ℝ (fderiv ℝ rho) q (0,F U) (0,F V)-
        fderiv ℝ rho q (0,Gamma (F U) (F V)))-⟪U,V⟫_ℝ := rfl
  constructor
  · intro U V
    have hCols (i : Fin 3) : |Bmixed U (coordinateVector i)| ≤ C*r^2*‖U‖ := by
      rw [hMixEval]
      exact hMixed i U
    have hh := abs_linear_map_le_of_coordinate_bounds (Bmixed U) (C*r^2*‖U‖) (by positivity) hCols V
    rw [hMixEval] at hh
    nlinarith only [hh]
  · intro U V
    have hCols (i j : Fin 3) : |Byy (coordinateVector i) (coordinateVector j)| ≤ C*r^2 := by
      rw [hYYEval]
      exact hYY i j
    have hh := abs_bilinear_map_le_of_coordinate_bounds Byy (C*r^2) (by positivity) hCols U V
    rw [hYYEval] at hh
    nlinarith only [hh]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
