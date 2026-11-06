import Calderon.MixedKernelConstruction.MixedKernelNativeEnergyPhaseJets
import Calderon.MixedKernelConstruction.MixedKernelProfileFrameCovector
import Calderon.MixedKernelConstruction.MixedKernelNativeSecondHessianBlock
import Calderon.MixedKernelConstruction.MixedKernelNativeJacobiFirstBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator
open NormalCoordinatesFrame ActualScalarPrincipalAdjoint ReferenceWeightedApproximation
open scoped ContDiff Topology InnerProductSpace

/-- Both exact energy covectors for the SAME actual common phase. -/
theorem native_energy_phase_covectors
    (rho : R3 × R3 → ℝ) (r : R3 → ℝ) (x y z : R3)
    (J F V : R3 →L[ℝ] R3)
    (hRho : DifferentiableAt ℝ rho (x,y)) (hr : DifferentiableAt ℝ r y)
    (hX : ∀ eta : R3, r y*fderiv ℝ rho (x,y) (J eta,0)=⟪z,eta⟫_ℝ)
    (hY : ∀ i : Fin 3, r y*fderiv ℝ rho (x,y) (0,F (coordinateVector i))=
      -(⟪z,coordinateVector i⟫_ℝ+(r y)^2*⟪z,V (coordinateVector i)⟫_ℝ)) :
    (∀ eta : R3, fderiv ℝ (nativeEnergyPhase (r y) rho r) (x,y) (J eta,0)=r y*⟪z,eta⟫_ℝ) ∧
    (∀ eta : R3, fderiv ℝ (nativeEnergyPhase (r y) rho r) (x,y) (0,F eta)=
      -(r y*⟪z+profileFrameCovectorVector r F y+(r y)^2 • V.adjoint z,eta⟫_ℝ)) := by
  constructor
  · intro eta
    rw [fderiv_nativeEnergyPhase_apply _ _ _ _ _ hRho hr]
    simp only [map_zero,mul_zero,sub_zero]
    have hs := congrArg (fun a : ℝ => r y*a) (hX eta)
    nlinarith only [hs]
  · intro eta
    let ell := (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inr ℝ R3 R3)
    have hCols : ∀ i : Fin 3, r y*ell (F (coordinateVector i))=
        -(⟪z,coordinateVector i⟫_ℝ+(r y)^2*⟪z,V (coordinateVector i)⟫_ℝ) := hY
    have hFull := covector_frame_columns_linear_extension ell F V (r y) z hCols eta
    change r y*fderiv ℝ rho (x,y) (0,F eta)=_ at hFull
    rw [fderiv_nativeEnergyPhase_apply _ _ _ _ _ hRho hr]
    rw [inner_add_left,inner_add_left,real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left,inner_profileFrameCovectorVector]
    change (r y)^2*fderiv ℝ rho (x,y) (0,F eta)-r y*fderiv ℝ r y (F eta)=_
    have hs := congrArg (fun a : ℝ => r y*a) hFull
    nlinarith only [hs]

/-- Exact operator norm control uses a true right inverse of the actual frame. -/
theorem covector_norm_le_of_frame_right_inverse
    (ell : R3 →L[ℝ] ℝ) (F Q : R3 →L[ℝ] R3) (r : ℝ) (n : R3)
    (hr : 0 ≤ r) (hInv : ∀ W : R3, F (Q W)=W)
    (hPair : ∀ eta : R3, ell (F eta)=-(r*⟪n,eta⟫_ℝ)) :
    ‖ell‖ ≤ r*‖Q‖*‖n‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro W
  have hh := hPair (Q W)
  rw [hInv] at hh
  calc
    ‖ell W‖ = r*|⟪n,Q W⟫_ℝ| := by
      rw [hh,norm_neg,norm_mul,Real.norm_eq_abs,abs_of_nonneg hr,Real.norm_eq_abs]
    _ ≤ r*(‖n‖*‖Q W‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hr
    _ ≤ r*(‖n‖*(‖Q‖*‖W‖)) := by
      gcongr
      exact Q.le_opNorm W
    _ = (r*‖Q‖*‖n‖)*‖W‖ := by ring

/-- The actual Jacobi adjoint error is estimated with its genuine isometric adjoint. -/
theorem norm_native_energy_frame_normal_le
    (z b : R3) (V : R3 →L[ℝ] R3) (r : ℝ) :
    ‖z+b+r^2 • V.adjoint z‖ ≤ ‖z‖+‖b‖+r^2*‖V‖*‖z‖ := by
  have hAdj : ‖V.adjoint‖=‖V‖ := ContinuousLinearMap.adjoint.norm_map V
  calc
    ‖z+b+r^2 • V.adjoint z‖ ≤ ‖z+b‖+‖r^2 • V.adjoint z‖ := norm_add_le _ _
    _ ≤ (‖z‖+‖b‖)+r^2*(‖V‖*‖z‖) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      gcongr
      · exact norm_add_le z b
      · rw [← hAdj]
        exact V.adjoint.le_opNorm z
    _ = ‖z‖+‖b‖+r^2*‖V‖*‖z‖ := by ring

/-- The literal smooth inverse frame has a compact bound chosen before all small parameters. -/
theorem exists_packet_frame_right_inverse_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ B : ℝ, 0 < B ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho →
        ‖referenceGramFrameInverse S.g1 L (lam,y)‖ ≤ B ∧
        ∀ W : R3, conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
          (referenceGramFrameInverse S.g1 L (lam,y) W)=W := by
  let K : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall P.y0 (4*P.rho)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (contDiff_referenceGramFrameInverse S.g1 S.g1_admissible L).continuous.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro lam hlam y hy
  have ha : (lam,y)∈K := ⟨hlam,by simpa only [mem_closedBall,dist_eq_norm] using hy⟩
  refine ⟨(hB (lam,y) ha).trans ((le_abs_self B).trans (by linarith)),?_⟩
  intro W
  have hh := congrArg (fun A : R3 →L[ℝ] R3 => A W)
    (referenceGramFrame_isInvertible S.g1 S.g1_admissible L (lam,y)).self_comp_inverse
  simpa only [referenceGramFrameInverse,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh

/-- The original square bootstrap controls the original unsquared radius covector. -/
theorem radius_mul_beta_le_of_square_bootstrap
    (r beta eps : ℝ) (hr : 0 ≤ r) (hbeta : 1 ≤ beta) (hBoot : r*beta^2 ≤ eps) :
    r*beta ≤ eps := by
  have h0 : 0 ≤ beta := by linarith
  have hh : beta ≤ beta^2 := by nlinarith only [hbeta]
  exact (mul_le_mul_of_nonneg_left hh hr).trans hBoot

/-- No beta is replaced: this is the exact original actualReferenceBeta bootstrap. -/
theorem norm_actual_radius_frame_covector_le_of_original_bootstrap
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar) (y : R3) (eps : ℝ)
    (hbeta : 1 ≤ actualReferenceBeta S.g1 L lam delta Rstar p y)
    (hBoot : referenceRadius delta Rstar p L y*(actualReferenceBeta S.g1 L lam delta Rstar p y)^2 ≤ eps) :
    ‖profileFrameCovectorVector (referenceRadius delta Rstar p L)
      (conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)) y‖ ≤ eps := by
  rw [norm_actual_radius_frame_covector_eq_radius_mul_beta S L lam delta Rstar p hdelta hRstar y]
  exact radius_mul_beta_le_of_square_bootstrap _ _ _
    (referenceRadius_pos delta Rstar p L y hdelta hRstar).le hbeta hBoot

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
