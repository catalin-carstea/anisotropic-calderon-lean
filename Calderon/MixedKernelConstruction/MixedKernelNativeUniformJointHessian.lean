import Calderon.MixedKernelConstruction.MixedKernelNativeJointHessianError
import Calderon.MixedKernelConstruction.MixedKernelAffineProductHessian
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff Topology InnerProductSpace

/-- One packet constant controls the full SAME-family actual joint covariant Hessian. -/
theorem exists_packet_joint_reference_hessian_error
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0<C ∧ ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ P.centers,
      ∀ r : ℝ, 0<r → r ≤ min 1 (4*P.rho) → ∀ z : R3, ‖z‖=1 →
      let x := packetEndpoint S L P lam y r z
      let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
      let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
      let M := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
      let Gamma := coordinateConnectionField (inverseMetricField M) M
      ∀ rho : R3 × R3 → ℝ, ContDiffAt ℝ 2 rho (x,y) →
      (∀ᶠ b : R3 × R3 in 𝓝 (y,z), rho (packetEndpoint S L P lam b.1 r b.2,b.1)=(⟪b.2,b.2⟫_ℝ-1)/2) →
      ∀ U V : R3,
      |r^2*(fderiv ℝ (fderiv ℝ rho) (x,y) (J U,F V) (J U,F V)-
        fderiv ℝ rho (x,y) (Gamma x (J U) (J U),Gamma y (F V) (F V)))-‖U-V‖^2| ≤ 
          C*r^2*(‖U‖+‖V‖)^2 := by
  obtain ⟨C,hC,H⟩ := exists_packet_common_native_phase_hessian_bounds S L P
  refine ⟨9*C,by positivity,?_⟩
  intro lam hlam y hy r hr hrCap z hz x J F M Gamma rho hRho hFamily U V
  obtain ⟨W,tau,hW,hxy,hTau,_hZero,hTauFamily,_hCov1,_hCov2,hX,hM,hY⟩ := H lam hlam y hy r hr hrCap z hz
  have hTauAt : ContDiffAt ℝ 2 tau (x,y) := (hTau.contDiffAt (hW.mem_nhds hxy)).of_le (by simp)
  have hEq : tau=ᶠ[𝓝 (x,y)]rho := packet_phases_eventuallyEq_of_family_identity S L P lam hlam r hr
    (hrCap.trans (min_le_right _ _)) y hy z (by simp only [mem_closedBall,dist_zero_right,hz];norm_num)
    tau rho hTauFamily hFamily
  have hD : fderiv ℝ tau (x,y)=fderiv ℝ rho (x,y) := hEq.fderiv_eq
  have hD2 : fderiv ℝ (fderiv ℝ tau) (x,y)=fderiv ℝ (fderiv ℝ rho) (x,y) := hEq.fderiv.fderiv_eq
  obtain ⟨hMix,hYY⟩ := native_hessian_column_estimates_extend tau (x,y) J F (Gamma y) r C hC.le hM hY
  apply native_reference_joint_hessian_error rho (x,y) hRho J F (Gamma x) (Gamma y) r (9*C) U V
  · have hx := hX U U
    rw [coordinateHessian_fst_slice_eq_product tau x y (J U) (J U) (Gamma x) hTauAt,hD2,hD,real_inner_self_eq_norm_sq] at hx
    apply hx.trans
    have hm := mul_le_mul_of_nonneg_right (show C ≤ 9*C by linarith) (by positivity : 0 ≤ r^2*‖U‖*‖U‖)
    nlinarith only [hm]
  · have hm := hMix U V
    rw [hD2] at hm
    apply hm.trans
    gcongr <;> linarith
  · have hy := hYY V V
    rw [hD2,hD,real_inner_self_eq_norm_sq] at hy
    convert hy using 1 <;> ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
