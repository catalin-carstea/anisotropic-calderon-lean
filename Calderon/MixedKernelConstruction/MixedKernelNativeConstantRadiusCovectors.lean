import Calderon.MixedKernelConstruction.MixedKernelNativeSecondCovector
import Calderon.MixedKernelConstruction.MixedKernelNativeConstantRadiusPhase
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- Both exact native covectors, with constant construction radius and arbitrary nearby z. -/
theorem packet_constant_radius_phase_covectors_of_identity
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r0 : ℝ) (hrpos : 0 < r0) (y : R3) (hy : y ∈ P.centers)
    (hr : r0 ≤ 4*P.rho) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (rho : R3 × R3 → ℝ)
    (hRho : ContDiffAt ℝ ∞ rho (packetEndpoint S L P lam y r0 z,y))
    (hfamily : ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
      rho (packetEndpoint S L P lam b.1 r0 b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) :
    let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r0),z))
    let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
    let x := packetEndpoint S L P lam y r0 z
    (∀ X : R3, fderiv ℝ rho (x,y) (X,0) =
      r0⁻¹*⟪z,ContinuousLinearMap.inverse J X⟫_ℝ) ∧
    (∀ i : Fin 3, r0*fderiv ℝ rho (x,y) (0,F (coordinateVector i)) =
      -(⟪z,coordinateVector i⟫_ℝ+
        r0^2*⟪z,referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i (lam,((y,r0),z))⟫_ℝ)) := by
  intro J F x
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  let Theta : R3 × R3 → R3 := fun b => (P.Phi lam b 1).1
  let FF : R3 → R3 →L[ℝ] R3 := fun u => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,u)
  let Gamma := coordinateConnectionField
    (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
    (metricOperatorField (conformalReferenceMatrix S.g1 L lam))
  let r : R3 → ℝ := fun _ => r0
  let E : R3 × R3 → R3 := fun b => packetEndpoint S L P lam b.1 r0 b.2
  have hTh : ContDiff ℝ ∞ Theta := hTheta.comp (contDiff_const.prodMk contDiff_id)
  have hFF : ContDiff ℝ ∞ FF :=
    (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).comp
      (contDiff_const.prodMk contDiff_id)
  have hRad : ContDiff ℝ ∞ r := contDiff_const
  have hEsmooth : ContDiff ℝ ∞ E :=
    hTh.comp (contDiff_fst.prodMk (((hFF.comp contDiff_fst).clm_apply contDiff_snd).const_smul r0))
  have hInv : J.IsInvertible := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r0
    (by rw [abs_of_pos hrpos];exact hr) z hz
  have hSlice : HasFDerivAt (packetEndpoint S L P lam y r0) (r0 • J) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun a => (P.Phi lam a 1).1)
      (fun u => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,u)) hTh y z r0
  have hFixed : ∀ᶠ w in 𝓝 z, rho (packetEndpoint S L P lam y r0 w,y) = (⟪w,w⟫_ℝ-1)/2 :=
    (continuousAt_const.prodMk continuousAt_id).eventually hfamily
  have hfirst (X : R3) : fderiv ℝ rho (x,y) (X,0) =
      r0⁻¹*⟪z,ContinuousLinearMap.inverse J X⟫_ℝ :=
    first_partial_formula_of_normalized_sphere_identity rho (packetEndpoint S L P lam y r0) r0 J
      x y z hrpos.ne' hRho hSlice rfl hInv hFixed X
  refine ⟨hfirst,?_⟩
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
    hRho (hEsmooth.differentiable (by simp) (y,z)).hasFDerivAt rfl hInv homega hDE hH hfirst hfamily
  have hDr : fderiv ℝ r y = 0 := (hasFDerivAt_const (𝕜 := ℝ) r0 y).fderiv
  simpa only [hDr,ContinuousLinearMap.zero_apply,zero_mul,add_zero,X,V] using hh

/-- The actual open inverse phase realizes BOTH covector identities on a joint neighborhood. -/
theorem exists_packet_constant_radius_covector_germs
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r0 : ℝ) (hrpos : 0 < r0) (y : R3) (hy : y ∈ P.centers)
    (hr : r0 ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let x := packetEndpoint S L P lam y r0 z
    ∃ U : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
      IsOpen U ∧ (x,y) ∈ U ∧ ContDiffOn ℝ ∞ rho U ∧ rho (x,y) = 0 ∧
      (∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 r0 b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) ∧
      ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((b.1,r0),b.2))
        let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,b.1)
        let xb := packetEndpoint S L P lam b.1 r0 b.2
        (∀ X : R3, fderiv ℝ rho (xb,b.1) (X,0) =
          r0⁻¹*⟪b.2,ContinuousLinearMap.inverse J X⟫_ℝ) ∧
        (∀ i : Fin 3, r0*fderiv ℝ rho (xb,b.1) (0,F (coordinateVector i)) =
          -(⟪b.2,coordinateVector i⟫_ℝ+
            r0^2*⟪b.2,referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i
              (lam,((b.1,r0),b.2))⟫_ℝ)) := by
  intro x
  obtain ⟨U,rho,hU,hxy,hRho,hzero,_,_,hfamily⟩ :=
    exists_packet_constant_radius_open_phase S L P lam hlam r0 hrpos y hy hr z hz
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  let Theta : R3 × R3 → R3 := fun b => (P.Phi lam b 1).1
  let FF : R3 → R3 →L[ℝ] R3 := fun u => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,u)
  have hTh : ContDiff ℝ ∞ Theta := hTheta.comp (contDiff_const.prodMk contDiff_id)
  have hFF : ContDiff ℝ ∞ FF :=
    (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).comp
      (contDiff_const.prodMk contDiff_id)
  have hE : ContDiff ℝ ∞ (fun b : R3 × R3 => packetEndpoint S L P lam b.1 r0 b.2) :=
    hTh.comp (contDiff_fst.prodMk (((hFF.comp contDiff_fst).clm_apply contDiff_snd).const_smul r0))
  have hC : ContinuousAt (fun b : R3 × R3 => (packetEndpoint S L P lam b.1 r0 b.2,b.1))
      (y,z) := (hE.continuous.continuousAt).prodMk continuousAt_fst
  have hCenter : ∀ᶠ b : R3 × R3 in 𝓝 (y,z), b.1 ∈ P.centers :=
    continuousAt_fst.eventually (P.centers_open.mem_nhds hy)
  have hBall : ∀ᶠ b : R3 × R3 in 𝓝 (y,z), b.2 ∈ ball (0 : R3) 2 := by
    apply continuousAt_snd.eventually
    apply isOpen_ball.mem_nhds
    simp only [mem_ball,dist_zero_right,hz]
    norm_num
  have hfamilyEq : (fun b : R3 × R3 => rho (packetEndpoint S L P lam b.1 r0 b.2,b.1)) =ᶠ[𝓝 (y,z)]
      (fun b => (⟪b.2,b.2⟫_ℝ-1)/2) := hfamily
  refine ⟨U,rho,hU,hxy,hRho,hzero,hfamily,?_⟩
  filter_upwards [hCenter,hBall,hC.eventually (hU.mem_nhds hxy),hfamilyEq.eventuallyEq_nhds]
    with b hb hbz hbU hloc
  exact packet_constant_radius_phase_covectors_of_identity S L P lam hlam r0 hrpos b.1 hb hr b.2
    (ball_subset_closedBall hbz) rho (hRho.contDiffAt (hU.mem_nhds hbU)) hloc

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
