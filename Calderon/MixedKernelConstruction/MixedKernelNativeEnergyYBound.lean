import Calderon.MixedKernelConstruction.MixedKernelNativeEnergyCovectors
import Calderon.MixedKernelConstruction.MixedKernelActualSecondConnection
import Calderon.MixedKernelConstruction.MixedKernelConnectionPerturbation
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator
open NormalCoordinatesFrame ActualScalarPrincipalAdjoint ReferenceWeightedApproximation
open scoped ContDiff Topology InnerProductSpace

/-- A bounded actual normal and true inverse frame give the required O(r) covector. -/
theorem native_energy_covector_norm_le_of_bounds
    (ell : R3 →L[ℝ] ℝ) (F Q V : R3 →L[ℝ] R3) (z b : R3) (r B D : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hz : ‖z‖=1) (hb : ‖b‖ ≤ 1) (hQ : ‖Q‖ ≤ B) (hV : ‖V‖ ≤ D)
    (hInv : ∀ W : R3, F (Q W)=W)
    (hPair : ∀ eta : R3, ell (F eta)=-(r*⟪z+b+r^2 • V.adjoint z,eta⟫_ℝ)) :
    ‖ell‖ ≤ (B*(2+D))*r := by
  have hr2 : r^2 ≤ 1 := by nlinarith only [hr,hr1]
  have hn := norm_native_energy_frame_normal_le z b V r
  rw [hz,mul_one] at hn
  have hnBound : ‖z+b+r^2 • V.adjoint z‖ ≤ 2+D := by
    have hErr : r^2*‖V‖ ≤ D := by
      calc
        r^2*‖V‖ ≤ 1*D := mul_le_mul hr2 hV (norm_nonneg V) (by norm_num)
        _ = D := one_mul D
    linarith
  have hh := covector_norm_le_of_frame_right_inverse ell F Q r _ hr hInv hPair
  calc
    ‖ell‖ ≤ r*‖Q‖*‖z+b+r^2 • V.adjoint z‖ := hh
    _ ≤ r*B*(2+D) := by gcongr
    _ = (B*(2+D))*r := by ring

/-- The actual packet's compact constants precede every small profile parameter. -/
theorem exists_packet_actual_energy_y_covector_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y ∈ P.centers, ∀ (delta Rstar eps : ℝ) (p : ℕ),
      0 < delta → 0 < Rstar → eps ≤ 1 →
      let r := referenceRadius delta Rstar p L
      let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
      ∀ z : R3, ‖z‖=1 → r y ≤ min 1 (4*P.rho) →
      let x := packetEndpoint S L P lam y (r y) z
      ∀ rho : R3 × R3 → ℝ, DifferentiableAt ℝ rho (x,y) →
      (∀ i : Fin 3, r y*fderiv ℝ rho (x,y) (0,F (coordinateVector i))=
        -(⟪z,coordinateVector i⟫_ℝ+(r y)^2*⟪z,referenceFramedJacobiVelocityRemainder
          S.g1 L P.Phi i (lam,((y,r y),z))⟫_ℝ)) →
      1 ≤ actualReferenceBeta S.g1 L lam delta Rstar p y →
      r y*(actualReferenceBeta S.g1 L lam delta Rstar p y)^2 ≤ eps →
      ‖(fderiv ℝ (nativeEnergyPhase (r y) rho r) (x,y)).comp
        (ContinuousLinearMap.inr ℝ R3 R3)‖ ≤ C*r y := by
  obtain ⟨B,hB,HB⟩ := exists_packet_frame_right_inverse_bound S L P
  obtain ⟨D,hD,HD⟩ := exists_packet_jacobi_synthesis_bound S L P
  refine ⟨B*(2+D),by positivity,?_⟩
  intro lam hlam y hy delta Rstar eps p hd hR he r F z hz hrCap x rho hRho hY hb hBoot
  have hrPos : 0 < r y := referenceRadius_pos delta Rstar p L y hd hR
  have hrDiff : DifferentiableAt ℝ r y :=
    (contDiff_referenceRadius_actual delta Rstar p L hd hR).differentiable (by simp) y
  have hyRoom : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  obtain ⟨hQ,hInv⟩ := HB lam hlam y hyRoom
  let Q := referenceGramFrameInverse S.g1 L (lam,y)
  let V := frameOperator (fun i => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r y),z)))
  let b := profileFrameCovectorVector r F y
  let ell := (fderiv ℝ (nativeEnergyPhase (r y) rho r) (x,y)).comp (ContinuousLinearMap.inr ℝ R3 R3)
  have hzClosed : z∈closedBall (0 : R3) 2 := by
    simp only [mem_closedBall,dist_zero_right,hz];norm_num
  have hV : ‖V‖ ≤ D := HD lam hlam y hyRoom (r y)
    (by rw [abs_of_pos hrPos];exact hrCap.trans (min_le_right _ _)) z hzClosed
  have hb1 : ‖b‖ ≤ 1 :=
    (norm_actual_radius_frame_covector_le_of_original_bootstrap S L lam delta Rstar p hd hR y eps hb hBoot).trans he
  let ellRho := (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inr ℝ R3 R3)
  have hCols : ∀ i : Fin 3, r y*ellRho (F (coordinateVector i))=
      -(⟪z,coordinateVector i⟫_ℝ+(r y)^2*⟪z,V (coordinateVector i)⟫_ℝ) := by
    intro i
    simpa only [ellRho,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,V,frameOperator_coordinateVector] using hY i
  have hPair (eta : R3) : ell (F eta)=-(r y*⟪z+b+(r y)^2 • V.adjoint z,eta⟫_ℝ) := by
    have hFull := covector_frame_columns_linear_extension ellRho F V (r y) z hCols eta
    change r y*fderiv ℝ rho (x,y) (0,F eta)=_ at hFull
    change fderiv ℝ (nativeEnergyPhase (r y) rho r) (x,y) (0,F eta)=_
    rw [fderiv_nativeEnergyPhase_apply _ _ _ _ _ hRho hrDiff]
    simp only [inner_add_left,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left,b,
      inner_profileFrameCovectorVector]
    change (r y)^2*fderiv ℝ rho (x,y) (0,F eta)-r y*fderiv ℝ r y (F eta)=_
    have hs := congrArg (fun a : ℝ => r y*a) hFull
    nlinarith only [hs]
  exact native_energy_covector_norm_le_of_bounds ell F Q V z b (r y) B D hrPos.le
    (hrCap.trans (min_le_left _ _)) hB.le hD.le hz hb1 hQ hV hInv hPair

/-- The genuine scalar yy-Hessian correction is O(epsilon r squared). -/
theorem native_energy_y_hessian_connection_error_le
    (ell : R3 →L[ℝ] ℝ) (H : R3 →L[ℝ] R3 →L[ℝ] ℝ)
    (Gamma Gamma0 : R3 →L[ℝ] R3 →L[ℝ] R3) (U V : R3) (C D eps r : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (heps : 0 ≤ eps) (hr : 0 ≤ r)
    (hell : ‖ell‖ ≤ C*r) (hGamma : ‖Gamma-Gamma0‖ ≤ D*eps*r) :
    |(H U V-ell (Gamma U V))-(H U V-ell (Gamma0 U V))| ≤
      (C*D)*eps*r^2*‖U‖*‖V‖ := by
  calc
    _ ≤ ‖ell‖*‖Gamma-Gamma0‖*‖U‖*‖V‖ := hessian_connection_error_le ell H Gamma Gamma0 U V
    _ ≤ (C*r)*(D*eps*r)*‖U‖*‖V‖ := by gcongr
    _ = (C*D)*eps*r^2*‖U‖*‖V‖ := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
