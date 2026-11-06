import Calderon.MixedKernelConstruction.MixedKernelNativeMixedHessianBlock
import Calderon.MixedKernelConstruction.MixedKernelNativeJacobiFirstBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- Restricting a genuine joint derivative to the second coordinate cannot increase its norm. -/
theorem norm_fderiv_snd_slice_le (V : R3 × R3 → R3) (y z : R3)
    (hV : DifferentiableAt ℝ V (y,z)) :
    ‖fderiv ℝ (fun w => V (y,w)) z‖ ≤ ‖fderiv ℝ V (y,z)‖ := by
  have hMap := (hasFDerivAt_const (𝕜 := ℝ) y z).prodMk (hasFDerivAt_id z)
  have hSlice := hV.hasFDerivAt.comp z hMap
  simp only [Function.comp_def] at hSlice
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro U
  rw [hSlice.fderiv]
  change ‖fderiv ℝ V (y,z) (0,U)‖ ≤ ‖fderiv ℝ V (y,z)‖*‖U‖
  simpa only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg U)] using
    (fderiv ℝ V (y,z)).le_opNorm ((0 : R3),U)

/-- The exact mixed covector formula has a quadratic geometric column error. -/
theorem mixed_hessian_column_error_of_formula
    (r D H : ℝ) (z e U V : R3) (DV : R3 →L[ℝ] R3)
    (hD : 0 ≤ D) (hz : ‖z‖=1) (hV : ‖V‖ ≤ D) (hDV : ‖DV‖ ≤ D)
    (hFormula : r^2*H = -⟪U,e⟫_ℝ-r^2*(⟪U,V⟫_ℝ+⟪z,DV U⟫_ℝ)) :
    |r^2*H+⟪U,e⟫_ℝ| ≤ (2*D)*r^2*‖U‖ := by
  have h1 : |⟪U,V⟫_ℝ| ≤ D*‖U‖ := by
    calc
      |⟪U,V⟫_ℝ| ≤ ‖U‖*‖V‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖U‖*D := mul_le_mul_of_nonneg_left hV (norm_nonneg U)
      _ = D*‖U‖ := mul_comm _ _
  have h2 : |⟪z,DV U⟫_ℝ| ≤ D*‖U‖ := by
    have h := abs_real_inner_le_norm z (DV U)
    rw [hz,one_mul] at h
    exact h.trans ((DV.le_opNorm U).trans (mul_le_mul_of_nonneg_right hDV (norm_nonneg U)))
  have heq : r^2*H+⟪U,e⟫_ℝ = -(r^2*(⟪U,V⟫_ℝ+⟪z,DV U⟫_ℝ)) := by linarith only [hFormula]
  rw [heq,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg r)]
  calc
    r^2*|⟪U,V⟫_ℝ+⟪z,DV U⟫_ℝ| ≤ r^2*(|⟪U,V⟫_ℝ|+|⟪z,DV U⟫_ℝ|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (sq_nonneg r)
    _ ≤ r^2*(D*‖U‖+D*‖U‖) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (sq_nonneg r)
    _ = (2*D)*r^2*‖U‖ := by ring

/-- A uniform quadratic mixed-column error for an actual open native phase, before arbitrary packet parameters. -/
theorem exists_packet_mixed_hessian_column_error_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, y ∈ P.centers → ∀ r : ℝ, 0 < r → r ≤ 4*P.rho →
      ∀ z : R3, ‖z‖=1 →
        let x := packetEndpoint S L P lam y r z
        let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
        let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
        ∃ U0 : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
          IsOpen U0 ∧ (x,y) ∈ U0 ∧ ContDiffOn ℝ ∞ rho U0 ∧ rho (x,y)=0 ∧
          (∀ᶠ b : R3 × R3 in 𝓝 (y,z),
            rho (packetEndpoint S L P lam b.1 r b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) ∧
          ∀ (i : Fin 3) (U : R3),
            |r^2*fderiv ℝ (fderiv ℝ rho) (x,y) (J U,0) (0,F (coordinateVector i))+
              ⟪U,coordinateVector i⟫_ℝ| ≤ C*r^2*‖U‖ := by
  obtain ⟨D,hD,HD⟩ := exists_packet_jacobi_first_bounds S L P
  refine ⟨2*D,by linarith,?_⟩
  intro lam hlam y hy r hrpos hr z hz x J F
  have hyClosed : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hrAbs : |r| ≤ 4*P.rho := by simpa only [abs_of_pos hrpos] using hr
  have hzClosed : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  obtain ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,Hformula⟩ :=
    exists_packet_constant_radius_mixed_hessian_formula S L P lam hlam r hrpos y hy hr z hz
  refine ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,?_⟩
  intro i U
  let VJ : R3 × R3 → R3 := fun b => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i
    (lam,((b.1,r),b.2))
  have hBounds := HD lam hlam y hyClosed r hrAbs z hzClosed i
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hInv := packet_closedRoom_normalizedJacobian_isInvertible S L P lam hlam y hyClosed r hrAbs z hzClosed
  have hVFull := contDiffAt_referenceFramedJacobiVelocityRemainder S.g1 S.g1_admissible L P.Phi hTheta i (lam,((y,r),z)) hInv
  have hVJ : ContDiffAt ℝ ∞ VJ (y,z) := by
    simpa only [VJ,Function.comp_def] using hVFull.comp (y,z)
      (contDiffAt_const.prodMk ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd))
  have hSlice : ‖fderiv ℝ (fun w => VJ (y,w)) z‖ ≤ D :=
    (norm_fderiv_snd_slice_le VJ y z (hVJ.differentiableAt (by simp))).trans hBounds.2
  exact mixed_hessian_column_error_of_formula r D
    (fderiv ℝ (fderiv ℝ rho) (x,y) (J U,0) (0,F (coordinateVector i)))
    z (coordinateVector i) U (VJ (y,z)) (fderiv ℝ (fun w => VJ (y,w)) z)
    (by linarith) hz hBounds.1 hSlice (Hformula i U)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
