import Calderon.MixedKernelConstruction.MixedKernelNativeMixedHessianBlock
import Calderon.MixedKernelConstruction.MixedKernelNativeFixedXTangent
import Calderon.MixedKernelConstruction.MixedKernelNativeAngularSkew
import Calderon.MetricHessianQuadratic
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- Extend the exact frame-column covector identity by genuine finite linearity. -/
theorem covector_frame_columns_linear_extension
    (ell : R3 →L[ℝ] ℝ) (F V : R3 →L[ℝ] R3) (r : ℝ) (z : R3)
    (hCols : ∀ i : Fin 3, r*ell (F (coordinateVector i)) =
      -(⟪z,coordinateVector i⟫_ℝ+r^2*⟪z,V (coordinateVector i)⟫_ℝ)) :
    ∀ eta : R3, r*ell (F eta) = -(⟪z,eta⟫_ℝ+r^2*⟪z,V eta⟫_ℝ) := by
  intro eta
  have hSum : eta = ∑ i : Fin 3, eta i • coordinateVector i := by
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr eta]
    simp only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,coordinateVector]
  have hInner := congrArg (fun A : R3 => ⟪z,A⟫_ℝ) hSum
  simp only [inner_sum,real_inner_smul_right] at hInner
  have hVInner := congrArg (fun A : R3 => ⟪z,V A⟫_ℝ) hSum
  simp only [map_sum,map_smul,inner_sum,real_inner_smul_right] at hVInner
  calc
    r*ell (F eta) = ∑ i : Fin 3, eta i*(r*ell (F (coordinateVector i))) := by
      conv_lhs => rw [hSum]
      simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin 3, eta i*(-(⟪z,coordinateVector i⟫_ℝ+r^2*⟪z,V (coordinateVector i)⟫_ℝ)) := by
      simp_rw [hCols]
    _ = -(⟪z,eta⟫_ℝ+r^2*⟪z,V eta⟫_ℝ) := by
      rw [hInner,hVInner,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Differentiate the genuine y-covector germ along a parameter tangent fixing physical x. -/
theorem second_variable_covector_germ_derivative
    (rho : R3 × R3 → ℝ) (E V : R3 × R3 → R3) (F : R3 → R3 →L[ℝ] R3)
    (DE DV : (R3 × R3) →L[ℝ] R3) (DF : R3 →L[ℝ] R3 →L[ℝ] R3)
    (r : ℝ) (x y z X Zp e : R3)
    (hRho : ContDiffAt ℝ 2 rho (x,y)) (hx : E (y,z) = x)
    (hE : HasFDerivAt E DE (y,z)) (hF : HasFDerivAt F DF y) (hV : HasFDerivAt V DV (y,z))
    (hDE : DE (X,Zp) = 0)
    (hGerm : ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
      r*fderiv ℝ rho (E b,b.1) (0,F b.1 e) = -(⟪b.2,e⟫_ℝ+r^2*⟪b.2,V b⟫_ℝ)) :
    r*(fderiv ℝ (fderiv ℝ rho) (x,y) (0,X) (0,F y e)+fderiv ℝ rho (x,y) (0,DF X e)) =
      -⟪Zp,e⟫_ℝ-r^2*(⟪Zp,V (y,z)⟫_ℝ+⟪z,DV (X,Zp)⟫_ℝ) := by
  have hdRho : DifferentiableAt ℝ (fderiv ℝ rho) (x,y) :=
    (hRho.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdRho' : HasFDerivAt (fderiv ℝ rho) (fderiv ℝ (fderiv ℝ rho) (x,y)) (E (y,z),y) := by
    rw [hx]
    exact hdRho.hasFDerivAt
  have hMap := hE.prodMk (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z)))
  have hOuter := hdRho'.comp (y,z) hMap
  have hFPar := hF.comp (y,z) (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,z)))
  have hW := (hasFDerivAt_const (𝕜 := ℝ) (0 : R3) (y,z)).prodMk
    (hFPar.clm_apply (hasFDerivAt_const e (y,z)))
  have hLeft := (hOuter.clm_apply hW).const_smul r
  have hLinear := (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,z))).inner ℝ (hasFDerivAt_const e (y,z))
  have hPair := (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,z))).inner ℝ hV
  have hRight := (hLinear.add (hPair.const_smul (r^2))).neg
  simp only [Function.comp_def] at hLeft hRight
  have hActual := hRight.congr_of_eventuallyEq hGerm
  have hh := congrArg (fun A : (R3 × R3) →L[ℝ] ℝ => A (X,Zp)) (hLeft.unique hActual)
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply,
    Prod.fst,Prod.snd,map_zero,zero_add,add_zero,inner_zero_left,inner_zero_right,smul_eq_mul,hDE,hx] at hh
  change r*(fderiv ℝ rho (x,y) (0,DF X e)+
      fderiv ℝ (fderiv ℝ rho) (x,y) (0,X) (0,F y e)) =
      -(⟪Zp,e⟫_ℝ+r^2*(⟪z,DV (X,Zp)⟫_ℝ+⟪Zp,V (y,z)⟫_ℝ)) at hh
  nlinarith only [hh]

/-- The literal reference connection correction follows from the ACTUAL frame derivative identity. -/
theorem covariant_second_block_of_covector_germ
    (ell : (R3 × R3) →L[ℝ] ℝ) (B : (R3 × R3) →L[ℝ] (R3 × R3) →L[ℝ] ℝ)
    (F V Omega : R3 →L[ℝ] R3) (Gamma : R3 →L[ℝ] R3 →L[ℝ] R3)
    (r R : ℝ) (z X e DFxe : R3)
    (hDerivative : r*(B (0,X) (0,F e)+ell (0,DFxe)) = R)
    (hFrame : DFxe+Gamma X (F e) = -F (Omega e))
    (hCov : ∀ eta : R3, r*ell (0,F eta) = -(⟪z,eta⟫_ℝ+r^2*⟪z,V eta⟫_ℝ)) :
    r^2*(B (0,X) (0,F e)-ell (0,Gamma X (F e))) =
      r*R-r*(⟪z,Omega e⟫_ℝ+r^2*⟪z,V (Omega e)⟫_ℝ) := by
  have hScalar := congrArg (fun A : R3 => ell (0,A)) hFrame
  have hAdd : ((0 : R3),DFxe+Gamma X (F e)) =
      ((0 : R3),DFxe)+((0 : R3),Gamma X (F e)) := by simp
  have hNeg : ((0 : R3),-F (Omega e)) = -((0 : R3),F (Omega e)) := by simp
  rw [hAdd,hNeg,map_add,map_neg] at hScalar
  have hScaled := congrArg (fun q : ℝ => r^2*q) hScalar
  calc
    r^2*(B (0,X) (0,F e)-ell (0,Gamma X (F e))) =
        r*(r*(B (0,X) (0,F e)+ell (0,DFxe)))+r*(r*ell (0,F (Omega e))) := by
      nlinarith only [hScaled]
    _ = _ := by rw [hDerivative,hCov];ring

/-- One actual open phase realizes the full reference yy formula on every native frame column. -/
theorem exists_packet_constant_radius_second_hessian_formula
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (hrpos : 0 < r) (y : R3) (hy : y ∈ P.centers)
    (hr : r ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let x := packetEndpoint S L P lam y r z
    let F : R3 → R3 →L[ℝ] R3 := fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y)
    let Gamma := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
      (metricOperatorField (conformalReferenceMatrix S.g1 L lam))
    let VR : (R3 × R3) → R3 →L[ℝ] R3 := fun b => frameOperator
      (fun k => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi k (lam,((b.1,r),b.2)))
    ∃ U0 : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
      IsOpen U0 ∧ (x,y) ∈ U0 ∧ ContDiffOn ℝ ∞ rho U0 ∧ rho (x,y) = 0 ∧
      (∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 r b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) ∧
      ∀ i j : Fin 3,
        let X := F y (coordinateVector i)
        let Omega := framedParallelAngularOperator F Gamma y X
        let Zp := Omega z-r⁻¹ • coordinateVector i-r • VR (y,z) (coordinateVector i)
        let Vj : R3 × R3 → R3 := fun b => VR b (coordinateVector j)
        r^2*(fderiv ℝ (fderiv ℝ rho) (x,y) (0,X) (0,F y (coordinateVector j))-
          fderiv ℝ rho (x,y) (0,Gamma y X (F y (coordinateVector j)))) =
          -r*⟪Zp,coordinateVector j⟫_ℝ-
            r^3*(⟪Zp,Vj (y,z)⟫_ℝ+⟪z,fderiv ℝ Vj (y,z) (X,Zp)⟫_ℝ)-
            r*⟪z,Omega (coordinateVector j)⟫_ℝ-
            r^3*⟪z,VR (y,z) (Omega (coordinateVector j))⟫_ℝ := by
  intro x F Gamma VR
  obtain ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,hCovGerm⟩ :=
    exists_packet_constant_radius_covector_germs S L P lam hlam r hrpos y hy hr z hz
  let E : R3 × R3 → R3 := fun b => packetEndpoint S L P lam b.1 r b.2
  let ell : (R3 × R3) →L[ℝ] ℝ := fderiv ℝ rho (x,y)
  let ell2 : R3 →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inr ℝ R3 R3)
  have hPoint := Filter.Eventually.self_of_nhds hCovGerm
  have hCols (k : Fin 3) : r*ell2 (F y (coordinateVector k)) =
      -(⟪z,coordinateVector k⟫_ℝ+r^2*⟪z,VR (y,z) (coordinateVector k)⟫_ℝ) := by
    change r*ell (0,F y (coordinateVector k)) = _
    simp only [VR,frameOperator_coordinateVector]
    exact hPoint.2 k
  have hCov : ∀ eta : R3, r*ell (0,F y eta) = -(⟪z,eta⟫_ℝ+r^2*⟪z,VR (y,z) eta⟫_ℝ) :=
    covector_frame_columns_linear_extension ell2 (F y) (VR (y,z)) r z hCols
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  let Theta : R3 × R3 → R3 := fun b => (P.Phi lam b 1).1
  have hTh : ContDiff ℝ ∞ Theta := hTheta.comp (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).comp
      (contDiff_const.prodMk contDiff_id)
  have hE : ContDiff ℝ ∞ E := hTh.comp
    (contDiff_fst.prodMk (((hF.comp contDiff_fst).clm_apply contDiff_snd).const_smul r))
  have hInv := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r
    (by rw [abs_of_pos hrpos];exact hr) z (by simp only [mem_closedBall,dist_zero_right,hz];norm_num)
  refine ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,?_⟩
  intro i j X Omega Zp Vj
  have hFixed : fderiv ℝ E (y,z) (X,Zp) = 0 := by
    simpa only [VR,frameOperator_coordinateVector,Omega,framedParallelAngularOperator_apply,X,Zp] using
      packet_constant_radius_fixed_x_tangent S L P lam hlam r hrpos y hy hr z
        (by simp only [mem_closedBall,dist_zero_right,hz];norm_num) i
  have hVFull := contDiffAt_referenceFramedJacobiVelocityRemainder S.g1 S.g1_admissible L P.Phi hTheta
    j (lam,((y,r),z)) hInv
  have hVj : ContDiffAt ℝ ∞ Vj (y,z) := by
    simpa only [Vj,VR,frameOperator_coordinateVector,Function.comp_def] using
      hVFull.comp (y,z) (contDiffAt_const.prodMk
        ((contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd))
  have hGerm : ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
      r*fderiv ℝ rho (E b,b.1) (0,F b.1 (coordinateVector j)) =
        -(⟪b.2,coordinateVector j⟫_ℝ+r^2*⟪b.2,Vj b⟫_ℝ) := by
    filter_upwards [hCovGerm] with b hb
    simpa only [Vj,VR,frameOperator_coordinateVector] using hb.2 j
  have hDerivative := second_variable_covector_germ_derivative rho E Vj F (fderiv ℝ E (y,z))
    (fderiv ℝ Vj (y,z)) (fderiv ℝ F y) r x y z X Zp (coordinateVector j)
    ((hRho.contDiffAt (hU0.mem_nhds hxy)).of_le (by simp)) rfl
    (hE.differentiable (by simp) (y,z)).hasFDerivAt (hF.differentiable (by simp) y).hasFDerivAt
    (hVj.differentiableAt (by simp)).hasFDerivAt hFixed hGerm
  have hFrame : fderiv ℝ F y X (coordinateVector j)+Gamma y X (F y (coordinateVector j)) =
      -F y (Omega (coordinateVector j)) := by
    have hh := frame_apply_parallelAngularVelocity F Gamma y X (coordinateVector j)
      (referenceGramFrame_isInvertible S.g1 S.g1_admissible L (lam,y))
    change F y (Omega (coordinateVector j)) = -(fderiv ℝ F y X (coordinateVector j)+
      Gamma y X (F y (coordinateVector j))) at hh
    simpa only [neg_neg] using (congrArg (fun W : R3 => -W) hh).symm
  have hFormula := covariant_second_block_of_covector_germ ell (fderiv ℝ (fderiv ℝ rho) (x,y))
    (F y) (VR (y,z)) Omega (Gamma y) r
    (-⟪Zp,coordinateVector j⟫_ℝ-r^2*(⟪Zp,Vj (y,z)⟫_ℝ+⟪z,fderiv ℝ Vj (y,z) (X,Zp)⟫_ℝ))
    z X (coordinateVector j) (fderiv ℝ F y X (coordinateVector j)) hDerivative hFrame hCov
  convert hFormula using 1 <;> ring

/-- Native skewness cancels every apparent first-order geometric yy term EXACTLY. -/
theorem second_block_leading_cancellation
    (Omega : R3 →L[ℝ] R3) (r : ℝ) (hr : r ≠ 0) (z e f V : R3)
    (hSkew : ⟪Omega z,f⟫_ℝ = -⟪z,Omega f⟫_ℝ) :
    -r*⟪Omega z-r⁻¹ • e-r • V,f⟫_ℝ-r*⟪z,Omega f⟫_ℝ =
      ⟪e,f⟫_ℝ+r^2*⟪V,f⟫_ℝ := by
  simp only [inner_sub_left,real_inner_smul_left,hSkew]
  field_simp [hr]
  <;> ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
