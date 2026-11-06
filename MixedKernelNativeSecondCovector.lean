import MixedKernelNativeFirstCovector
import MixedKernelParallelAngularTangency
import Calderon.ActualFramedJacobiVelocityRemainder
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- The moving-radius endpoint retains its radial derivative in the actual parallel direction. -/
theorem fderiv_variable_radius_framedEndpoint_parallel_horizontal
    (Theta : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (Gamma : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (r : R3 → ℝ)
    (hTheta : ContDiff ℝ ∞ Theta) (hF : ContDiff ℝ ∞ F)
    (hr : ContDiff ℝ ∞ r) (y X z : R3) (hInv : (F y).IsInvertible) :
    fderiv ℝ (fun b : R3 × R3 => Theta (b.1,r b.1 • F b.1 b.2))
      (y,z) (X,framedParallelAngularVelocity F Gamma y X z) =
      fderiv ℝ Theta (y,r y • F y z) (X,-r y • Gamma y X (F y z)) +
        (fderiv ℝ r y X) • fderiv ℝ Theta (y,r y • F y z) (0,F y z) := by
  have hFp := (hF.differentiable (by simp) y).hasFDerivAt.comp (y,z)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z)))
  have hV := hFp.clm_apply (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,z)))
  have hR := (hr.differentiable (by simp) y).hasFDerivAt.comp (y,z)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z)))
  have hP := (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z))).prodMk (hR.smul hV)
  have hc := (hTheta.differentiable (by simp) (y,r y • F y z)).hasFDerivAt.comp (y,z) hP
  simp only [Function.comp_def,Pi.smul_apply'] at hc
  rw [hc.fderiv]
  change fderiv ℝ Theta (y,r y • F y z)
    (X,r y • (F y (framedParallelAngularVelocity F Gamma y X z) + fderiv ℝ F y X z) +
      (fderiv ℝ r y X) • F y z) = _
  rw [frame_apply_parallelAngularVelocity F Gamma y X z hInv]
  have halg : -(fderiv ℝ F y X z + Gamma y X (F y z)) + fderiv ℝ F y X z =
      -Gamma y X (F y z) := by abel
  rw [halg]
  have hv : (X,r y • -Gamma y X (F y z) + (fderiv ℝ r y X) • F y z) =
      (X,-r y • Gamma y X (F y z)) + (fderiv ℝ r y X) • ((0 : R3),F y z) := by
    simp only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero,smul_neg,neg_smul]
  rw [hv,map_add,map_smul]

/-- The joint sphere identity fixes the second covector, with the genuine radial term. -/
theorem second_partial_formula_of_moving_sphere_identity
    (rho : R3 × R3 → ℝ) (E : R3 × R3 → R3)
    (DE : (R3 × R3) →L[ℝ] R3) (J : R3 →L[ℝ] R3)
    (r s : ℝ) (x y z X omega H e V : R3)
    (hr : r ≠ 0) (hRho : ContDiffAt ℝ ∞ rho (x,y))
    (hE : HasFDerivAt E DE (y,z)) (hx : x = E (y,z))
    (hJ : J.IsInvertible) (homega : ⟪z,omega⟫_ℝ = 0)
    (hDE : DE (X,omega) = H+s • J z)
    (hH : ContinuousLinearMap.inverse J H = e+r^2 • V)
    (hfirst : ∀ Y : R3, fderiv ℝ rho (x,y) (Y,0) =
      r⁻¹ * ⟪z,ContinuousLinearMap.inverse J Y⟫_ℝ)
    (hidentity : ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
      rho (E b,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) :
    r * fderiv ℝ rho (x,y) (0,X) =
      -(⟪z,e⟫_ℝ+s*⟪z,z⟫_ℝ+r^2*⟪z,V⟫_ℝ) := by
  have hmodel : HasFDerivAt (fun w : R3 => (⟪w,w⟫_ℝ-1)/2) (innerSL ℝ z) z := by
    have hh := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.sub_const 1).const_smul ((2 : ℝ)⁻¹)
    have hfactor : (2 : ℝ)⁻¹ • (2 • innerSL ℝ z) = innerSL ℝ z := by
      rw [two_smul,smul_add,← add_smul]
      norm_num
    have hfunc : (fun w : R3 => (⟪w,w⟫_ℝ-1)/2) =
        (2 : ℝ)⁻¹ • (fun w : R3 => ‖w‖^2-1) := by
      funext w
      simp only [Pi.smul_apply,smul_eq_mul,real_inner_self_eq_norm_sq,div_eq_mul_inv]
      ring
    rw [hfunc]
    simpa only [hfactor] using hh
  have hRho' : HasFDerivAt rho (fderiv ℝ rho (x,y)) (E (y,z),y) := by
    rw [← hx]
    exact (hRho.differentiableAt (by simp)).hasFDerivAt
  have hpair := hE.prodMk (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z)))
  have hcompose := hRho'.comp (y,z) hpair
  have hmod := hmodel.comp (y,z) (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,z)))
  have hjet := hcompose.unique (hmod.congr_of_eventuallyEq hidentity)
  have hv := congrArg (fun A : (R3 × R3) →L[ℝ] ℝ => A (X,omega)) hjet
  change fderiv ℝ rho (x,y) (DE (X,omega),X) = ⟪z,omega⟫_ℝ at hv
  rw [homega,hDE] at hv
  have hJI : ContinuousLinearMap.inverse J (J z) = z := by
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => A z) hJ.inverse_comp_self
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh
  have hfirstH := hfirst (H+s • J z)
  rw [map_add,map_smul,hH,hJI,inner_add_right,inner_add_right,inner_smul_right,inner_smul_right] at hfirstH
  have hscale : r*fderiv ℝ rho (x,y) (H+s • J z,0) =
      ⟪z,e⟫_ℝ+r^2*⟪z,V⟫_ℝ+s*⟪z,z⟫_ℝ := by
    rw [hfirstH,← mul_assoc,mul_inv_cancel₀ hr,one_mul]
  have hsplit : (H+s • J z,X) = (H+s • J z,(0 : R3)) + ((0 : R3),X) := by simp
  rw [hsplit,map_add] at hv
  have hh := congrArg (fun a : ℝ => r*a) hv
  simp only [mul_add,mul_zero] at hh
  linarith

/-- Both actual first covectors come from one phase for the SAME moving reference-radius spheres. -/
theorem exists_packet_referenceRadius_covectors
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hR : 0 < Rstar)
    (y : R3) (hy : y ∈ P.centers)
    (hr : referenceRadius delta Rstar p L y ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let r0 := referenceRadius delta Rstar p L y
    let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r0),z))
    let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
    let x := packetEndpoint S L P lam y r0 z
    ∃ U : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
      IsOpen U ∧ (x,y) ∈ U ∧ ContDiffOn ℝ ∞ rho U ∧ rho (x,y) = 0 ∧
      (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ∧
      (∀ X : R3, fderiv ℝ rho (x,y) (X,0) =
        r0⁻¹ * ⟪z,ContinuousLinearMap.inverse J X⟫_ℝ) ∧
      (∀ i : Fin 3,
        r0*fderiv ℝ rho (x,y) (0,F (coordinateVector i)) =
          -(⟪z,coordinateVector i⟫_ℝ +
            fderiv ℝ (referenceRadius delta Rstar p L) y (F (coordinateVector i)) +
            r0^2*⟪z,referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r0),z))⟫_ℝ)) ∧
      ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 (referenceRadius delta Rstar p L b.1) b.2,b.1) =
          (⟪b.2,b.2⟫_ℝ-1)/2 := by
  intro r0 J F x
  obtain ⟨U,rho,hU,hxy,hsmooth,hzero,hne,hfirst,hfamily⟩ :=
    exists_packet_referenceRadius_first_covector S L P lam hlam delta Rstar p hd hR y hy hr z hz
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  let Theta : R3 × R3 → R3 := fun b => (P.Phi lam b 1).1
  let FF : R3 → R3 →L[ℝ] R3 := fun u => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,u)
  let Gamma := coordinateConnectionField
    (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
    (metricOperatorField (conformalReferenceMatrix S.g1 L lam))
  let r : R3 → ℝ := referenceRadius delta Rstar p L
  let E : R3 × R3 → R3 := fun b => packetEndpoint S L P lam b.1 (r b.1) b.2
  have hTh : ContDiff ℝ ∞ Theta := hTheta.comp (contDiff_const.prodMk contDiff_id)
  have hFF : ContDiff ℝ ∞ FF :=
    (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).comp
      (contDiff_const.prodMk contDiff_id)
  have hRad : ContDiff ℝ ∞ r := contDiff_referenceRadius_actual delta Rstar p L hd hR
  have hEsmooth : ContDiff ℝ ∞ E := by
    exact hTh.comp (contDiff_fst.prodMk ((hRad.comp contDiff_fst).smul
      ((hFF.comp contDiff_fst).clm_apply contDiff_snd)))
  have hrpos : 0 < r0 := referenceRadius_pos delta Rstar p L y hd hR
  have hInv : J.IsInvertible := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r0
    (by rw [abs_of_pos hrpos];exact hr) z (by simp only [mem_closedBall,dist_zero_right,hz];norm_num)
  have hfirst' (X : R3) : fderiv ℝ rho (x,y) (X,0) =
      r0⁻¹*⟪z,ContinuousLinearMap.inverse J X⟫_ℝ := hfirst X
  refine ⟨U,rho,hU,hxy,hsmooth,hzero,hne,hfirst',?_,hfamily⟩
  intro i
  let X := F (coordinateVector i)
  let omega := framedParallelAngularVelocity FF Gamma y X z
  let H := referenceFramedCenterHorizontalVelocity S.g1 L P.Phi i (lam,((y,r0),z))
  let V := referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r0),z))
  have homega : ⟪z,omega⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact native_parallelAngularVelocity_inner_eq_zero S.g1 S.g1_admissible L lam y X z
  have hDE : fderiv ℝ E (y,z) (X,omega) = H+(fderiv ℝ r y X) • J z :=
    fderiv_variable_radius_framedEndpoint_parallel_horizontal Theta FF Gamma r hTh hFF hRad y X z
      (referenceGramFrame_isInvertible S.g1 S.g1_admissible L (lam,y))
  have hH : ContinuousLinearMap.inverse J H = coordinateVector i+r0^2 • V :=
    referenceFramedCenterHorizontalVelocity_inverse_quadratic S.g1 S.g1_admissible L P.y0 P.Phi P.B
      hEnd lam hlam y (P.centers_room y hy).2 r0 z i hInv
  have hh := second_partial_formula_of_moving_sphere_identity rho E (fderiv ℝ E (y,z)) J
    r0 (fderiv ℝ r y X) x y z X omega H (coordinateVector i) V hrpos.ne'
    (hsmooth.contDiffAt (hU.mem_nhds hxy)) (hEsmooth.differentiable (by simp) (y,z)).hasFDerivAt
    rfl hInv homega hDE hH hfirst' hfamily
  simpa only [real_inner_self_eq_norm_sq,hz,one_pow,mul_one] using hh

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
