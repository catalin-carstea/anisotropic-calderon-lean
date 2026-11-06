import Calderon.MixedKernelConstruction.MixedKernelNativeFirstHessianBlock
import Calderon.MixedKernelConstruction.MixedKernelNativeMixedHessianBound
import Calderon.MixedKernelConstruction.MixedKernelNativeSecondHessianUniform
import Calderon.MixedKernelConstruction.MixedKernelNativePairOpenImage
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- Both covectors and ALL reference Hessian blocks belong to ONE actual smooth native phase. -/
theorem exists_packet_common_native_phase_hessian_bounds
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, y ∈ P.centers → ∀ r : ℝ, 0 < r → r ≤ min 1 (4*P.rho) →
      ∀ z : R3, ‖z‖=1 →
        let x := packetEndpoint S L P lam y r z
        let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
        let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
        let M := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
        let Gamma := coordinateConnectionField (inverseMetricField M) M
        ∃ U0 : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
          IsOpen U0 ∧ (x,y) ∈ U0 ∧ ContDiffOn ℝ ∞ rho U0 ∧ rho (x,y)=0 ∧
          (∀ᶠ b : R3 × R3 in 𝓝 (y,z),
            rho (packetEndpoint S L P lam b.1 r b.2,b.1)=(⟪b.2,b.2⟫_ℝ-1)/2) ∧
          (∀ X : R3, fderiv ℝ rho (x,y) (X,0)=r⁻¹*⟪z,ContinuousLinearMap.inverse J X⟫_ℝ) ∧
          (∀ i : Fin 3, r*fderiv ℝ rho (x,y) (0,F (coordinateVector i))=
            -(⟪z,coordinateVector i⟫_ℝ+r^2*⟪z,referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r),z))⟫_ℝ)) ∧
          (∀ U V : R3, |r^2*RadiusProfile.coordinateHessian (fun X => rho (X,y))
            (fun A B => Gamma x A B) x (J U) (J V)-⟪U,V⟫_ℝ| ≤ C*r^2*‖U‖*‖V‖) ∧
          (∀ (i : Fin 3) (U : R3), |r^2*fderiv ℝ (fderiv ℝ rho) (x,y) (J U,0) (0,F (coordinateVector i))+
            ⟪U,coordinateVector i⟫_ℝ| ≤ C*r^2*‖U‖) ∧
          (∀ i j : Fin 3, |r^2*(fderiv ℝ (fderiv ℝ rho) (x,y) (0,F (coordinateVector i)) (0,F (coordinateVector j))-
            fderiv ℝ rho (x,y) (0,Gamma y (F (coordinateVector i)) (F (coordinateVector j))))-
            ⟪coordinateVector i,coordinateVector j⟫_ℝ| ≤ C*r^2) := by
  obtain ⟨Cx,hCx,Hx⟩ := exists_packet_first_covariant_hessian_error_bound S L P
  obtain ⟨Cm,hCm,Hm⟩ := exists_packet_mixed_hessian_column_error_bound S L P
  obtain ⟨Cy,hCy,Hy⟩ := exists_packet_second_hessian_column_error_bound S L P
  let C : ℝ := Cx+Cm+Cy
  have hC : 0 < C := by dsimp [C];linarith
  have hCxC : Cx ≤ C := by dsimp [C];linarith
  have hCmC : Cm ≤ C := by dsimp [C];linarith
  have hCyC : Cy ≤ C := by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro lam hlam y hy r hrpos hr z hz x J F M Gamma
  have hrrho : r ≤ 4*P.rho := hr.trans (min_le_right _ _)
  have hzClosed : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  obtain ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,Hyy⟩ := Hy lam hlam y hy r hrpos hr z hz
  obtain ⟨V0,tau,hV0,htxy,hTau,htzero,htfamily,Hmixed⟩ := Hm lam hlam y hy r hrpos hrrho z hz
  have hEq : tau =ᶠ[𝓝 (x,y)] rho := packet_phases_eventuallyEq_of_family_identity
    S L P lam hlam r hrpos hrrho y hy z hzClosed tau rho htfamily hfamily
  have hFull2 : fderiv ℝ (fderiv ℝ tau) (x,y)=fderiv ℝ (fderiv ℝ rho) (x,y) := hEq.fderiv.fderiv_eq
  have hPoint : ContDiffAt ℝ ∞ rho (x,y) := hRho.contDiffAt (hU0.mem_nhds hxy)
  have hFixed : ∀ᶠ w in 𝓝 z, rho (packetEndpoint S L P lam y r w,y)=(⟪w,w⟫_ℝ-1)/2 :=
    (continuousAt_const.prodMk continuousAt_id).eventually hfamily
  obtain ⟨hCov1,hCov2⟩ := packet_constant_radius_phase_covectors_of_identity
    S L P lam hlam r hrpos y hy hrrho z hzClosed rho hPoint hfamily
  refine ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,hCov1,hCov2,?_,?_,?_⟩
  · intro U V
    exact (Hx lam hlam y hy r hrpos hrrho z hz rho hPoint hFixed U V).trans (by
      have hh := mul_le_mul_of_nonneg_right hCxC (by positivity : 0 ≤ r^2*‖U‖*‖V‖)
      nlinarith only [hh])
  · intro i U
    have hh := Hmixed i U
    rw [hFull2] at hh
    exact hh.trans (by
      have hb := mul_le_mul_of_nonneg_right hCmC (by positivity : 0 ≤ r^2*‖U‖)
      nlinarith only [hb])
  · intro i j
    exact (Hyy i j).trans (mul_le_mul_of_nonneg_right hCyC (sq_nonneg r))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
