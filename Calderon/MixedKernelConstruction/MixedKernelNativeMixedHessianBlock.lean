import Calderon.MixedKernelConstruction.MixedKernelNativeConstantRadiusCovectors
import Calderon.MixedKernelConstruction.MixedKernelNativeJacobiBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- Differentiate the actual second-covector germ through the actual first-variable endpoint. -/
theorem mixed_second_fderiv_of_constant_radius_covector_germ
    (rho : R3 × R3 → ℝ) (E V : R3 → R3) (J : R3 →L[ℝ] R3)
    (r : ℝ) (x y z Y e U : R3)
    (hRho : ContDiffAt ℝ 2 rho (x,y)) (hx : E z = x)
    (hE : HasFDerivAt E (r • J) z) (hV : DifferentiableAt ℝ V z)
    (hGerm : ∀ᶠ w in 𝓝 z,
      r*fderiv ℝ rho (E w,y) (0,Y) = -(⟪w,e⟫_ℝ+r^2*⟪w,V w⟫_ℝ)) :
    r^2*fderiv ℝ (fderiv ℝ rho) (x,y) (J U,0) (0,Y) =
      -⟪U,e⟫_ℝ-r^2*(⟪U,V z⟫_ℝ+⟪z,fderiv ℝ V z U⟫_ℝ) := by
  have hdRho : DifferentiableAt ℝ (fderiv ℝ rho) (x,y) :=
    (hRho.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdRho' : HasFDerivAt (fderiv ℝ rho) (fderiv ℝ (fderiv ℝ rho) (x,y)) (E z,y) := by
    rw [hx]
    exact hdRho.hasFDerivAt
  have hOuter := hdRho'.comp z (hE.prodMk (hasFDerivAt_const y z))
  have hLeft := (hOuter.clm_apply (hasFDerivAt_const ((0 : R3),Y) z)).const_smul r
  have hLinear := (hasFDerivAt_id (𝕜 := ℝ) z).inner ℝ (hasFDerivAt_const e z)
  have hPair := (hasFDerivAt_id (𝕜 := ℝ) z).inner ℝ hV.hasFDerivAt
  have hRight := (hLinear.add (hPair.const_smul (r^2))).neg
  simp only [Function.comp_def,Pi.smul_apply,Pi.smul_apply',smul_eq_mul] at hLeft hRight
  have hActual := hRight.congr_of_eventuallyEq hGerm
  have hh := congrArg (fun A : R3 →L[ℝ] ℝ => A U) (hLeft.unique hActual)
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,Prod.fst,Prod.snd,id_eq,map_zero,zero_add,add_zero,
    inner_zero_left,inner_zero_right,innerSL_apply_apply,smul_eq_mul] at hh
  have hScale : (r • J U,(0 : R3)) = r • (J U,(0 : R3)) := by simp
  rw [hScale,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at hh
  nlinarith only [hh]

/-- One actual open native phase realizes the exact mixed block for every frame column. -/
theorem exists_packet_constant_radius_mixed_hessian_formula
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (hrpos : 0 < r) (y : R3) (hy : y ∈ P.centers)
    (hr : r ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let x := packetEndpoint S L P lam y r z
    let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
    let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
    ∃ U0 : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
      IsOpen U0 ∧ (x,y) ∈ U0 ∧ ContDiffOn ℝ ∞ rho U0 ∧ rho (x,y) = 0 ∧
      (∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 r b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) ∧
      ∀ (i : Fin 3) (U : R3),
        let Vi : R3 → R3 := fun w => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r),w))
        r^2*fderiv ℝ (fderiv ℝ rho) (x,y) (J U,0) (0,F (coordinateVector i)) =
          -⟪U,coordinateVector i⟫_ℝ-r^2*(⟪U,Vi z⟫_ℝ+⟪z,fderiv ℝ Vi z U⟫_ℝ) := by
  intro x J F
  obtain ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,hCovGerm⟩ :=
    exists_packet_constant_radius_covector_germs S L P lam hlam r hrpos y hy hr z hz
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hE : HasFDerivAt (packetEndpoint S L P lam y r) (r • J) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun a => (P.Phi lam a 1).1)
      (fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y))
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) y z r
  have hInv : J.IsInvertible := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r
    (by rw [abs_of_pos hrpos];exact hr) z (by simp only [mem_closedBall,dist_zero_right,hz];norm_num)
  refine ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,?_⟩
  intro i U Vi
  have hVFull := contDiffAt_referenceFramedJacobiVelocityRemainder S.g1 S.g1_admissible L P.Phi hTheta
    i (lam,((y,r),z)) hInv
  have hVi : ContDiffAt ℝ ∞ Vi z :=
    hVFull.comp z (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hGerm : ∀ᶠ w in 𝓝 z,
      r*fderiv ℝ rho (packetEndpoint S L P lam y r w,y) (0,F (coordinateVector i)) =
        -(⟪w,coordinateVector i⟫_ℝ+r^2*⟪w,Vi w⟫_ℝ) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hCovGerm] with w hw
    exact hw.2 i
  exact mixed_second_fderiv_of_constant_radius_covector_germ rho (packetEndpoint S L P lam y r) Vi J
    r x y z (F (coordinateVector i)) (coordinateVector i) U
    ((hRho.contDiffAt (hU0.mem_nhds hxy)).of_le (by simp)) rfl hE
    (hVi.differentiableAt (by simp)) hGerm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
