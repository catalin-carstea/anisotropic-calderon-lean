import Calderon.MixedKernelConstruction.TaskInterface
import Calderon.MetricOperator
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator
open scoped ContDiff Topology

/-- Exact bilinear difference for the ORIGINAL coordinate Koszul connection. -/
theorem coordinateConnectionLinearMap_sub
    (Q Q0 : R3 →L[ℝ] R3) (D D0 : R3 →L[ℝ] R3 →L[ℝ] R3) :
    coordinateConnectionLinearMap Q D-coordinateConnectionLinearMap Q0 D0=
      coordinateConnectionLinearMap (Q-Q0) D+coordinateConnectionLinearMap Q0 (D-D0) := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  change (1/2 : ℝ) • Q (koszulLinearMap D U V)-(1/2 : ℝ) • Q0 (koszulLinearMap D0 U V)=
    (1/2 : ℝ) • (Q-Q0) (koszulLinearMap D U V)+(1/2 : ℝ) • Q0 (koszulLinearMap (D-D0) U V)
  simp only [map_sub,ContinuousLinearMap.sub_apply,smul_sub]
  abel

/-- Quantitative difference bound for the SAME native coordinate connection. -/
theorem norm_coordinateConnectionLinearMap_sub_le
    (Q Q0 : R3 →L[ℝ] R3) (D D0 : R3 →L[ℝ] R3 →L[ℝ] R3) :
    ‖coordinateConnectionLinearMap Q D-coordinateConnectionLinearMap Q0 D0‖ ≤
      (3/2 : ℝ)*(‖Q-Q0‖*‖D‖+‖Q0‖*‖D-D0‖) := by
  rw [coordinateConnectionLinearMap_sub]
  calc
    ‖coordinateConnectionLinearMap (Q-Q0) D+coordinateConnectionLinearMap Q0 (D-D0)‖ ≤
        ‖coordinateConnectionLinearMap (Q-Q0) D‖+‖coordinateConnectionLinearMap Q0 (D-D0)‖ := norm_add_le (coordinateConnectionLinearMap (Q-Q0) D) (coordinateConnectionLinearMap Q0 (D-D0))
    _ ≤ (3/2 : ℝ)*‖Q-Q0‖*‖D‖+(3/2 : ℝ)*‖Q0‖*‖D-D0‖ :=
      add_le_add (norm_coordinateConnectionLinearMap_le (Q-Q0) D) (norm_coordinateConnectionLinearMap_le Q0 (D-D0))
    _ = (3/2 : ℝ)*(‖Q-Q0‖*‖D‖+‖Q0‖*‖D-D0‖) := by ring

/-- The actual scalar covariant-Hessian error caused by a connection perturbation. -/
theorem hessian_connection_error_le
    (ell : R3 →L[ℝ] ℝ) (B : R3 →L[ℝ] R3 →L[ℝ] ℝ)
    (Gamma Gamma0 : R3 →L[ℝ] R3 →L[ℝ] R3) (U V : R3) :
    |(B U V-ell (Gamma U V))-(B U V-ell (Gamma0 U V))| ≤
      ‖ell‖*‖Gamma-Gamma0‖*‖U‖*‖V‖ := by
  have heq : (B U V-ell (Gamma U V))-(B U V-ell (Gamma0 U V))=
      -ell ((Gamma-Gamma0) U V) := by
    simp only [ContinuousLinearMap.sub_apply,map_sub]
    ring
  rw [heq,abs_neg]
  have hB : ‖(Gamma-Gamma0) U V‖ ≤ ‖Gamma-Gamma0‖*‖U‖*‖V‖ :=
    (((Gamma-Gamma0) U).le_opNorm V).trans
      (mul_le_mul_of_nonneg_right ((Gamma-Gamma0).le_opNorm U) (norm_nonneg V))
  have hh : |ell ((Gamma-Gamma0) U V)| ≤ ‖ell‖*‖(Gamma-Gamma0) U V‖ := by
    simpa only [Real.norm_eq_abs] using ell.le_opNorm ((Gamma-Gamma0) U V)
  exact hh.trans (by
    have h := mul_le_mul_of_nonneg_left hB (norm_nonneg ell)
    nlinarith only [h])

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
