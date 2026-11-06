import MixedKernelNativeConstantRadiusCovectors
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- The exact linear cancellation that fixes the physical first endpoint. -/
theorem product_derivative_fixed_endpoint_tangent
    (D : (R3 × R3) →L[ℝ] R3) (J : R3 →L[ℝ] R3)
    (r : ℝ) (hr : r ≠ 0) (X omega H e V : R3)
    (hSpatial : ∀ A : R3, D (0,A) = r • J A)
    (hHorizontal : D (X,omega) = H) (hH : H = J e+r^2 • J V) :
    D (X,omega-r⁻¹ • e-r • V) = 0 := by
  have hArg : (X,omega-r⁻¹ • e-r • V) =
      (X,omega)-r⁻¹ • ((0 : R3),e)-r • ((0 : R3),V) := by
    apply Prod.ext <;> simp
  rw [hArg,map_sub,map_sub,map_smul,map_smul,hHorizontal,hSpatial,hSpatial,hH]
  simp only [smul_smul,inv_mul_cancel₀ hr,one_smul,pow_two]
  module

/-- The SAME actual native horizontal Jacobi identities realize the physical-x-fixed tangent. -/
theorem packet_constant_radius_fixed_x_tangent
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (hrpos : 0 < r) (y : R3) (hy : y ∈ P.centers)
    (hr : r ≤ 4*P.rho) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) (i : Fin 3) :
    let F : R3 → R3 →L[ℝ] R3 := fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y)
    let Gamma := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
      (metricOperatorField (conformalReferenceMatrix S.g1 L lam))
    let X := F y (coordinateVector i)
    let omega := framedParallelAngularVelocity F Gamma y X z
    let Vi := referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r),z))
    fderiv ℝ (fun b : R3 × R3 => packetEndpoint S L P lam b.1 r b.2) (y,z)
      (X,omega-r⁻¹ • coordinateVector i-r • Vi) = 0 := by
  intro F Gamma X omega Vi
  let E : R3 × R3 → R3 := fun b => packetEndpoint S L P lam b.1 r b.2
  let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
  let H := referenceFramedCenterHorizontalVelocity S.g1 L P.Phi i (lam,((y,r),z))
  let Rad : R3 → ℝ := fun _ => r
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  let Theta : R3 × R3 → R3 := fun b => (P.Phi lam b 1).1
  have hTh : ContDiff ℝ ∞ Theta := hTheta.comp (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ ∞ F :=
    (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).comp
      (contDiff_const.prodMk contDiff_id)
  have hE : ContDiff ℝ ∞ E := hTh.comp
    (contDiff_fst.prodMk (((hF.comp contDiff_fst).clm_apply contDiff_snd).const_smul r))
  have hInv : J.IsInvertible := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r
    (by rw [abs_of_pos hrpos];exact hr) z hz
  have hSpatial (A : R3) : fderiv ℝ E (y,z) (0,A) = r • J A := by
    have h1 := (hE.differentiable (by simp) (y,z)).hasFDerivAt.comp z
      ((hasFDerivAt_const (𝕜 := ℝ) y z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
    have h2 : HasFDerivAt (packetEndpoint S L P lam y r) (r • J) z :=
      hasFDerivAt_framedScaledEndpoint_slice Theta F hTh y z r
    have hh := congrArg (fun A0 : R3 →L[ℝ] R3 => A0 A) (h1.unique h2)
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.smul_apply] using hh
  have hHorizontal0 : fderiv ℝ E (y,z) (X,omega) = H+(fderiv ℝ Rad y X) • J z :=
    fderiv_variable_radius_framedEndpoint_parallel_horizontal Theta F Gamma Rad hTh hF contDiff_const y X z
      (referenceGramFrame_isInvertible S.g1 S.g1_admissible L (lam,y))
  have hDr : fderiv ℝ Rad y = 0 := (hasFDerivAt_const (𝕜 := ℝ) r y).fderiv
  have hHorizontal : fderiv ℝ E (y,z) (X,omega) = H := by
    simpa only [hDr,ContinuousLinearMap.zero_apply,zero_smul,add_zero] using hHorizontal0
  have hInverse : ContinuousLinearMap.inverse J H = coordinateVector i+r^2 • Vi :=
    referenceFramedCenterHorizontalVelocity_inverse_quadratic S.g1 S.g1_admissible L P.y0 P.Phi P.B
      hEnd lam hlam y (P.centers_room y hy).2 r z i hInv
  have hH : H = J (coordinateVector i)+r^2 • J Vi := by
    have hh := congrArg (fun W : R3 => J W) hInverse
    simpa only [hInv.self_apply_inverse,map_add,map_smul] using hh
  exact product_derivative_fixed_endpoint_tangent (fderiv ℝ E (y,z)) J r hrpos.ne'
    X omega H (coordinateVector i) Vi hSpatial hHorizontal hH

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
