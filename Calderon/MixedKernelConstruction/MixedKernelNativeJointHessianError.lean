import Calderon.MixedKernelConstruction.MixedKernelNativeBilinearHessian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError
open scoped ContDiff Topology InnerProductSpace

/-- Bilinearity retains BOTH genuine mixed blocks when expanding a joint diagonal. -/
theorem product_bilinear_diagonal_split
    (B : (R3 × R3) →L[ℝ] (R3 × R3) →L[ℝ] ℝ) (X Y : R3)
    (hCross : B (0,Y) (X,0)=B (X,0) (0,Y)) :
    B (X,Y) (X,Y)=B (X,0) (X,0)+2*B (X,0) (0,Y)+B (0,Y) (0,Y) := by
  have hSplit : (X,Y)=(X,0)+(0,Y) := by simp
  conv_lhs => rw [hSplit]
  simp only [map_add,ContinuousLinearMap.add_apply]
  rw [hCross]
  ring

/-- The actual three-block error bounds control the same full joint quadratic form. -/
theorem product_bilinear_joint_error_of_native_blocks
    (B : (R3 × R3) →L[ℝ] (R3 × R3) →L[ℝ] ℝ) (J F : R3 →L[ℝ] R3)
    (r C : ℝ) (U V : R3)
    (hCross : B (0,F V) (J U,0)=B (J U,0) (0,F V))
    (hXX : |B (J U,0) (J U,0)-‖U‖^2|≤C*r^2*‖U‖^2)
    (hXY : |B (J U,0) (0,F V)+⟪U,V⟫_ℝ|≤C*r^2*‖U‖*‖V‖)
    (hYY : |B (0,F V) (0,F V)-‖V‖^2|≤C*r^2*‖V‖^2) :
    |B (J U,F V) (J U,F V)-‖U-V‖^2|≤C*r^2*(‖U‖+‖V‖)^2 := by
  have hForm := product_bilinear_diagonal_split B (J U) (F V) hCross
  have hNorm : ‖U-V‖^2=‖U‖^2-2*⟪U,V⟫_ℝ+‖V‖^2 := norm_sub_sq_real U V
  have hEq : B (J U,F V) (J U,F V)-‖U-V‖^2=
      (B (J U,0) (J U,0)-‖U‖^2)+2*(B (J U,0) (0,F V)+⟪U,V⟫_ℝ)+
        (B (0,F V) (0,F V)-‖V‖^2) := by rw [hForm,hNorm];ring
  rw [hEq]
  calc
    _ ≤ |B (J U,0) (J U,0)-‖U‖^2|+|2*(B (J U,0) (0,F V)+⟪U,V⟫_ℝ)|+
        |B (0,F V) (0,F V)-‖V‖^2| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |B (J U,0) (J U,0)-‖U‖^2|+2*|B (J U,0) (0,F V)+⟪U,V⟫_ℝ|+
        |B (0,F V) (0,F V)-‖V‖^2| := by rw [abs_mul];norm_num
    _ ≤ C*r^2*‖U‖^2+2*(C*r^2*‖U‖*‖V‖)+C*r^2*‖V‖^2 :=
      add_le_add (add_le_add hXX (mul_le_mul_of_nonneg_left hXY (by norm_num))) hYY
    _ = C*r^2*(‖U‖+‖V‖)^2 := by ring

/-- The SAME C2 phase's actual product covariant Hessian satisfies the full joint estimate. -/
theorem native_reference_joint_hessian_error
    (rho : R3 × R3 → ℝ) (q : R3 × R3) (hRho : ContDiffAt ℝ 2 rho q)
    (J F : R3 →L[ℝ] R3) (Gamma1 Gamma2 : R3 →L[ℝ] R3 →L[ℝ] R3)
    (r C : ℝ) (U V : R3)
    (hXX : |r^2*(fderiv ℝ (fderiv ℝ rho) q (J U,0) (J U,0)-
      fderiv ℝ rho q (Gamma1 (J U) (J U),0))-‖U‖^2|≤C*r^2*‖U‖^2)
    (hXY : |r^2*fderiv ℝ (fderiv ℝ rho) q (J U,0) (0,F V)+⟪U,V⟫_ℝ|≤C*r^2*‖U‖*‖V‖)
    (hYY : |r^2*(fderiv ℝ (fderiv ℝ rho) q (0,F V) (0,F V)-
      fderiv ℝ rho q (0,Gamma2 (F V) (F V)))-‖V‖^2|≤C*r^2*‖V‖^2) :
    |r^2*(fderiv ℝ (fderiv ℝ rho) q (J U,F V) (J U,F V)-
      fderiv ℝ rho q (Gamma1 (J U) (J U),Gamma2 (F V) (F V)))-‖U-V‖^2|≤
        C*r^2*(‖U‖+‖V‖)^2 := by
  let p1 := ContinuousLinearMap.fst ℝ R3 R3
  let p2 := ContinuousLinearMap.snd ℝ R3 R3
  let G1 := Gamma1.bilinearComp p1 p1
  let G2 := Gamma2.bilinearComp p2 p2
  let prodMap : (((R3 × R3) →L[ℝ] R3) × ((R3 × R3) →L[ℝ] R3)) →L[ℝ]
      ((R3 × R3) →L[ℝ] R3 × R3) := (ContinuousLinearMap.prodL ℝ).toContinuousLinearMap
  let GP := prodMap.comp (G1.prod G2)
  let ell := fderiv ℝ rho q
  let B := r^2 • (fderiv ℝ (fderiv ℝ rho) q-
    ((ContinuousLinearMap.compL ℝ (R3 × R3) (R3 × R3) ℝ) ell).comp GP)
  have hEval (W Z : R3 × R3) : B W Z=r^2*(fderiv ℝ (fderiv ℝ rho) q W Z-
      fderiv ℝ rho q (Gamma1 W.1 Z.1,Gamma2 W.2 Z.2)) := rfl
  have hCross : B (0,F V) (J U,0)=B (J U,0) (0,F V) := by
    rw [hEval,hEval]
    simp only [map_zero,ContinuousLinearMap.zero_apply,sub_zero]
    rw [(hRho.isSymmSndFDerivAt (by norm_num)) (0,F V) (J U,0)]
  have hXXB : |B (J U,0) (J U,0)-‖U‖^2|≤C*r^2*‖U‖^2 := by
    simpa only [hEval,map_zero,ContinuousLinearMap.zero_apply] using hXX
  have hCovZero : fderiv ℝ rho q ((0 : R3),(0 : R3))=0 := map_zero _
  have hXYB : |B (J U,0) (0,F V)+⟪U,V⟫_ℝ|≤C*r^2*‖U‖*‖V‖ := by
    simpa only [hEval,map_zero,ContinuousLinearMap.zero_apply,hCovZero,sub_zero] using hXY
  have hYYB : |B (0,F V) (0,F V)-‖V‖^2|≤C*r^2*‖V‖^2 := by
    simpa only [hEval,map_zero,ContinuousLinearMap.zero_apply] using hYY
  simpa only [hEval] using product_bilinear_joint_error_of_native_blocks B J F r C U V hCross hXXB hXYB hYYB

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
