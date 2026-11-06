import Calderon.MixedKernelConstruction.MixedKernelNativeJacobiBounds
import Calderon.MetricFrameOperator
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- ACTUAL Jacobi values and fixed-lambda/r joint center/angular derivatives, uniformly on the closed room. -/
theorem exists_packet_jacobi_first_bounds
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho → ∀ r : ℝ, |r| ≤ 4*P.rho →
      ∀ z ∈ closedBall (0 : R3) 2, ∀ i : Fin 3,
        ‖referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r),z))‖ ≤ D ∧
        ‖fderiv ℝ (fun b : R3 × R3 => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i
          (lam,((b.1,r),b.2))) (y,z)‖ ≤ D := by
  obtain ⟨D,hD,H⟩ := exists_packet_closedRoom_jacobi_bounds S L P 1
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  refine ⟨D+1,by linarith,?_⟩
  intro lam hlam y hy r hr z hz i
  let a : ReferenceEndpointVariables := (lam,((y,r),z))
  let VS : R3 × R3 → R3 := fun b => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i
    (lam,((b.1,r),b.2))
  have ha : a ∈ conformalReferenceFramedMetricRoom P.y0 (4*P.rho) :=
    ⟨hlam,⟨⟨by simpa only [mem_closedBall,dist_eq_norm] using hy,abs_le.mp hr⟩,hz⟩⟩
  have hValue : ‖referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i a‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using H 0 (by norm_num) a ha i
  have hFull : ‖fderiv ℝ (referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i) a‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_one] using H 1 le_rfl a ha i
  refine ⟨hValue.trans (by linarith),?_⟩
  have hInv := packet_closedRoom_normalizedJacobian_isInvertible S L P lam hlam y hy r hr z hz
  have hVFull := contDiffAt_referenceFramedJacobiVelocityRemainder S.g1 S.g1_admissible L P.Phi hTheta i a hInv
  have hMap := (hasFDerivAt_const (𝕜 := ℝ) lam (y,z)).prodMk
    (((hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z))).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) r (y,z))).prodMk
        (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,z))))
  have hSlice := (hVFull.differentiableAt (by simp)).hasFDerivAt.comp (y,z) hMap
  simp only [Function.comp_def] at hSlice
  change HasFDerivAt VS _ (y,z) at hSlice
  apply ContinuousLinearMap.opNorm_le_bound (fderiv ℝ VS (y,z)) (by linarith)
  intro U
  rw [hSlice.fderiv]
  change ‖fderiv ℝ (referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i) a
    ((0 : ℝ),((U.1,(0 : ℝ)),U.2))‖ ≤ (D+1)*‖U‖
  have hNorm : ‖((0 : ℝ),((U.1,(0 : ℝ)),U.2))‖ = ‖U‖ := by simp [Prod.norm_def]
  have hh := (fderiv ℝ (referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i) a).le_opNorm
    ((0 : ℝ),((U.1,(0 : ℝ)),U.2))
  rw [hNorm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hFull.trans (by linarith)) (norm_nonneg U))

/-- The ACTUAL Jacobi column synthesis has a uniform operator bound; no metric-frame property is assumed. -/
theorem exists_packet_jacobi_synthesis_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ D : ℝ, 0 < D ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho → ∀ r : ℝ, |r| ≤ 4*P.rho →
      ∀ z ∈ closedBall (0 : R3) 2,
        ‖frameOperator (fun i => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i
          (lam,((y,r),z)))‖ ≤ D := by
  obtain ⟨D,hD,H⟩ := exists_packet_jacobi_first_bounds S L P
  refine ⟨3*D,by linarith,?_⟩
  intro lam hlam y hy r hr z hz
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro eta
  rw [frameOperator_apply]
  calc
    ‖∑ i : Fin 3, eta i • referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r),z))‖ ≤
        ∑ i : Fin 3, ‖eta i • referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r),z))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖eta‖*D := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le eta i) (H lam hlam y hy r hr z hz i).1
        (norm_nonneg _) (norm_nonneg eta)
    _ = (3*D)*‖eta‖ := by simp [Fin.sum_univ_three];ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
