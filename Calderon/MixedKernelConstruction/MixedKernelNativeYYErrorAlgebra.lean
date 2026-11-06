import Calderon.MixedKernelConstruction.MixedKernelNativeSecondHessianBlock
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError
open scoped ContDiff InnerProductSpace Topology

/-- The actual fixed-x parameter tangent has a uniform bound only after multiplication by r. -/
theorem norm_scaled_fixed_x_tangent_le
    (Omega : R3 →L[ℝ] R3) (r K : ℝ) (z e V Zp : R3)
    (hr : 0 < r) (hr1 : r ≤ 1) (hK : 1 ≤ K)
    (hz : ‖z‖=1) (he : ‖e‖=1) (hO : ‖Omega‖ ≤ K) (hV : ‖V‖ ≤ K)
    (hZp : Zp=Omega z-r⁻¹ • e-r • V) :
    r*‖Zp‖ ≤ 1+2*K := by
  have hK0 : 0 ≤ K := by linarith
  have hrSq : r^2 ≤ 1 := by nlinarith
  have hOz : ‖Omega z‖ ≤ K := by
    simpa only [hz,mul_one] using (Omega.le_opNorm z).trans (mul_le_mul_of_nonneg_right hO (norm_nonneg z))
  have hFirst : ‖r • Omega z‖ ≤ K := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hOz hr.le).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hK0)
  have hSecond : ‖(r^2) • V‖ ≤ K := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
    exact (mul_le_mul_of_nonneg_left hV (sq_nonneg r)).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hrSq hK0)
  have hScale : r • Zp = r • Omega z-e-(r^2) • V := by
    rw [hZp]
    simp only [smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul,pow_two]
  have hNorm := norm_sub_le (r • Omega z-e) ((r^2) • V)
  have hNorm2 := norm_sub_le (r • Omega z) e
  have hScaled : ‖r • Zp‖ ≤ 1+2*K := by rw [hScale];linarith
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr] using hScaled

/-- Exact skew cancellation and actual operator bounds give a genuinely quadratic yy column error. -/
theorem second_hessian_column_error_of_formula
    (Omega VR : R3 →L[ℝ] R3) (DV : (R3 × R3) →L[ℝ] R3)
    (r K H : ℝ) (z e f X Vi Vj Zp : R3)
    (hr : 0 < r) (hr1 : r ≤ 1) (hK : 1 ≤ K)
    (hz : ‖z‖=1) (he : ‖e‖=1) (hf : ‖f‖=1)
    (hO : ‖Omega‖ ≤ K) (hVR : ‖VR‖ ≤ K) (hDV : ‖DV‖ ≤ K)
    (hX : ‖X‖ ≤ K) (hVi : ‖Vi‖ ≤ K) (hVj : ‖Vj‖ ≤ K)
    (hZp : Zp=Omega z-r⁻¹ • e-r • Vi)
    (hSkew : ⟪Omega z,f⟫_ℝ = -⟪z,Omega f⟫_ℝ)
    (hFormula : r^2*H = -r*⟪Zp,f⟫_ℝ-r^3*(⟪Zp,Vj⟫_ℝ+⟪z,DV (X,Zp)⟫_ℝ)-
      r*⟪z,Omega f⟫_ℝ-r^3*⟪z,VR (Omega f)⟫_ℝ) :
    |r^2*H-⟪e,f⟫_ℝ| ≤ (3*K+6*K^2)*r^2 := by
  have hK0 : 0 ≤ K := by linarith
  let A : ℝ := 1+2*K
  have hZ : r*‖Zp‖ ≤ A := norm_scaled_fixed_x_tangent_le Omega r K z e Vi Zp hr hr1 hK hz he hO hVi hZp
  have hXr : r*‖X‖ ≤ K := (mul_le_mul_of_nonneg_left hX hr.le).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hK0)
  have h1 : |⟪Vi,f⟫_ℝ| ≤ K := by
    simpa only [hf,mul_one] using (abs_real_inner_le_norm Vi f).trans (mul_le_mul_of_nonneg_right hVi (norm_nonneg f))
  have h2 : r*|⟪Zp,Vj⟫_ℝ| ≤ K*A := by
    calc
      r*|⟪Zp,Vj⟫_ℝ| ≤ r*(‖Zp‖*‖Vj‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hr.le
      _ ≤ r*(‖Zp‖*K) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVj (norm_nonneg Zp)) hr.le
      _ = K*(r*‖Zp‖) := by ring
      _ ≤ K*A := mul_le_mul_of_nonneg_left hZ hK0
  have hProd : ‖(X,Zp)‖ ≤ ‖X‖+‖Zp‖ := by
    rw [Prod.norm_def]
    exact max_le (by linarith [norm_nonneg Zp]) (by linarith [norm_nonneg X])
  have hD : ‖DV (X,Zp)‖ ≤ K*(‖X‖+‖Zp‖) :=
    (DV.le_opNorm (X,Zp)).trans ((mul_le_mul_of_nonneg_right hDV (norm_nonneg (X,Zp))).trans
      (mul_le_mul_of_nonneg_left hProd hK0))
  have h3 : r*|⟪z,DV (X,Zp)⟫_ℝ| ≤ K*(K+A) := by
    have hh : |⟪z,DV (X,Zp)⟫_ℝ| ≤ ‖DV (X,Zp)‖ := by simpa only [hz,one_mul] using abs_real_inner_le_norm z (DV (X,Zp))
    calc
      r*|⟪z,DV (X,Zp)⟫_ℝ| ≤ r*(K*(‖X‖+‖Zp‖)) := mul_le_mul_of_nonneg_left (hh.trans hD) hr.le
      _ = K*(r*‖X‖+r*‖Zp‖) := by ring
      _ ≤ K*(K+A) := mul_le_mul_of_nonneg_left (add_le_add hXr hZ) hK0
  have hOf : ‖Omega f‖ ≤ K := by
    simpa only [hf,mul_one] using (Omega.le_opNorm f).trans (mul_le_mul_of_nonneg_right hO (norm_nonneg f))
  have hVRf : ‖VR (Omega f)‖ ≤ K^2 :=
    (VR.le_opNorm (Omega f)).trans (by simpa only [pow_two] using mul_le_mul hVR hOf (norm_nonneg (Omega f)) hK0)
  have h4 : r*|⟪z,VR (Omega f)⟫_ℝ| ≤ K^2 := by
    have hInner : |⟪z,VR (Omega f)⟫_ℝ| ≤ ‖VR (Omega f)‖ := by
      simpa only [hz,one_mul] using abs_real_inner_le_norm z (VR (Omega f))
    have hh : |⟪z,VR (Omega f)⟫_ℝ| ≤ K^2 := hInner.trans hVRf
    exact (mul_le_mul_of_nonneg_left hh hr.le).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 (sq_nonneg K))
  have hCancel : -r*⟪Zp,f⟫_ℝ-r*⟪z,Omega f⟫_ℝ = ⟪e,f⟫_ℝ+r^2*⟪Vi,f⟫_ℝ := by
    rw [hZp]
    exact second_block_leading_cancellation Omega r hr.ne' z e f Vi hSkew
  have hError : r^2*H-⟪e,f⟫_ℝ = r^2*⟪Vi,f⟫_ℝ-r^3*⟪Zp,Vj⟫_ℝ-
      r^3*⟪z,DV (X,Zp)⟫_ℝ-r^3*⟪z,VR (Omega f)⟫_ℝ := by
    linear_combination hFormula+hCancel
  have hAbs : |r^2*H-⟪e,f⟫_ℝ| ≤ r^2*|⟪Vi,f⟫_ℝ|+r^3*|⟪Zp,Vj⟫_ℝ|+
      r^3*|⟪z,DV (X,Zp)⟫_ℝ|+r^3*|⟪z,VR (Omega f)⟫_ℝ| := by
    rw [hError]
    have hA1 := abs_add_le (r^2*⟪Vi,f⟫_ℝ) (-(r^3*⟪Zp,Vj⟫_ℝ))
    have hA2 := abs_add_le (r^2*⟪Vi,f⟫_ℝ-r^3*⟪Zp,Vj⟫_ℝ) (-(r^3*⟪z,DV (X,Zp)⟫_ℝ))
    have hA3 := abs_add_le (r^2*⟪Vi,f⟫_ℝ-r^3*⟪Zp,Vj⟫_ℝ-r^3*⟪z,DV (X,Zp)⟫_ℝ) (-(r^3*⟪z,VR (Omega f)⟫_ℝ))
    simp only [← sub_eq_add_neg,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg r),abs_of_pos (pow_pos hr 3)] at hA1 hA2 hA3
    linarith only [hA1,hA2,hA3]
  have hB1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
  have hB2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg r)
  have hB3 := mul_le_mul_of_nonneg_left h3 (sq_nonneg r)
  have hB4 := mul_le_mul_of_nonneg_left h4 (sq_nonneg r)
  have hPoly : r^2*K+r^2*(K*A)+r^2*(K*(K+A))+r^2*K^2 = (3*K+6*K^2)*r^2 := by dsimp [A];ring
  rw [← hPoly]
  nlinarith only [hAbs,hB1,hB2,hB3,hB4]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
