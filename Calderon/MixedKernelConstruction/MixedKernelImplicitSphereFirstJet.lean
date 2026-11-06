import Calderon.MixedKernelConstruction.MixedKernelNativePacketInverse
import Calderon.MixedKernelConstruction.MixedKernelSmoothPacketInverse
import Calderon.ActualScalarPrincipalAdjoint
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open scoped ContDiff InnerProductSpace Topology

/-- The actual radius-normalized physical variables supplied to the local normal inverse. -/
def normalizedPhaseArgument (lam : ℝ) (r : R3 → ℝ) (v : R3 × R3) :
    ReferenceNormalParameters × R3 :=
  ((lam,(v.2,r v.2)),(r v.2)⁻¹ • (v.1-v.2))

/-- A local defining phase for the same native spheres, represented by the actual inverse. -/
def implicitNormalSpherePhase (psi : ReferenceNormalParameters × R3 → R3)
    (lam : ℝ) (r : R3 → ℝ) (v : R3 × R3) : ℝ :=
  let Z := psi (normalizedPhaseArgument lam r v)
  (⟪Z,Z⟫_ℝ-1)/2

/-- Pulling the genuine local inverse equivalence back to the original endpoint. -/
theorem normal_inverse_eq_near (f : ReferenceNormalParameters × R3 → R3)
    (p : ReferenceNormalParameters) (z : R3) (psi : ReferenceNormalParameters × R3 → R3)
    (hf : ContinuousAt f (p,z))
    (hleft : ∀ᶠ b : (ReferenceNormalParameters × R3) × R3 in 𝓝 ((p,f (p,z)),z),
      f (b.1.1,b.2) = b.1.2 ↔ psi b.1 = b.2) :
    ∀ᶠ w in 𝓝 z, psi (p,f (p,w)) = w := by
  have hc : ContinuousAt (fun w : R3 => ((p,f (p,w)),w)) z := by
    exact (continuousAt_const.prodMk (hf.comp (continuousAt_const.prodMk continuousAt_id))).prodMk
      continuousAt_id
  filter_upwards [hc.eventually hleft] with w hw
  exact hw.mp rfl

/-- The phase is smooth at every positive-radius inverse point with actual smooth radius. -/
theorem contDiffAt_implicitNormalSpherePhase
    (psi : ReferenceNormalParameters × R3 → R3) (lam : ℝ) (r : R3 → ℝ) (x y : R3)
    (hr : ContDiffAt ℝ ∞ r y) (hr0 : r y ≠ 0)
    (hp : ContDiffAt ℝ ∞ psi (normalizedPhaseArgument lam r (x,y))) :
    ContDiffAt ℝ ∞ (implicitNormalSpherePhase psi lam r) (x,y) := by
  have hArg : ContDiffAt ℝ ∞ (normalizedPhaseArgument lam r) (x,y) := by
    unfold normalizedPhaseArgument
    fun_prop
  have hZ := hp.comp (x,y) hArg
  exact ((hZ.inner ℝ hZ).sub contDiffAt_const).div_const 2

/-- The exact radial sphere identity forces the first partial covector to be nonzero. -/
theorem first_partial_ne_zero_of_radial_sphere_identity
    (rho : R3 × R3 → ℝ) (E : R3 → R3) (r : ℝ) (x y z : R3)
    (hRho : ContDiffAt ℝ ∞ rho (x,y)) (hE : DifferentiableAt ℝ E z)
    (hx : x = y+r • E z) (hz : ‖z‖ = 1)
    (hlocal : ∀ᶠ w in 𝓝 z, rho (y+r • E w,y) = (⟪w,w⟫_ℝ-1)/2) :
    (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 := by
  intro hzero
  let curve : ℝ → R3 := fun t => y+r • E ((1+t) • z)
  have hw : HasDerivAt (fun t : ℝ => (1+t) • z) z 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))).smul_const z using 1 <;> simp
  have hEw : HasDerivAt (fun t : ℝ => E ((1+t) • z)) ((fderiv ℝ E z) z) 0 :=
    hE.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hw (by simp)
  have hcurve : DifferentiableAt ℝ curve 0 :=
    ((hasDerivAt_const (0 : ℝ) y).add (hEw.const_smul r)).differentiableAt
  have hpair := hcurve.hasDerivAt.prodMk (hasDerivAt_const (0 : ℝ) y)
  have hpt : (curve 0,y) = (x,y) := by
    simp only [curve,add_zero,one_smul]
    rw [hx]
  have hcompose := (hRho.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hpair hpt.symm
  have hDzero : fderiv ℝ rho (x,y) (deriv curve 0,0) = 0 := by
    have hh := congrArg (fun A : R3 →L[ℝ] ℝ => A (deriv curve 0)) hzero
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.zero_apply] using hh
  have hder0 : HasDerivAt (fun t : ℝ => rho (curve t,y)) 0 0 := by
    simpa only [Function.comp_def,hDzero] using hcompose
  have hmodel : HasDerivAt (fun t : ℝ => (⟪(1+t) • z,(1+t) • z⟫_ℝ-1)/2) 1 0 := by
    convert ((hw.inner ℝ hw).sub_const 1).div_const 2 using 1 <;>
      simp [real_inner_self_eq_norm_sq,hz]
  have hwt : Tendsto (fun t : ℝ => (1+t) • z) (𝓝 0) (𝓝 z) := by
    simpa only [add_zero,one_smul] using hw.continuousAt.tendsto
  have hEq : (fun t : ℝ => rho (curve t,y)) =ᶠ[𝓝 0]
      (fun t : ℝ => (⟪(1+t) • z,(1+t) • z⟫_ℝ-1)/2) := by
    filter_upwards [hwt.eventually hlocal] with t ht
    exact ht
  have hder1 : HasDerivAt (fun t : ℝ => rho (curve t,y)) 1 0 :=
    hmodel.congr_of_eventuallyEq hEq
  have hh : (0 : ℝ) = 1 := hder0.unique hder1
  norm_num at hh

/-- The ACTUAL reference-radius native sphere has a smooth local phase with nonzero first partial. -/
theorem exists_packet_referenceRadius_first_phase
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hR : 0 < Rstar)
    (y : R3) (hy : y ∈ P.centers)
    (hr : referenceRadius delta Rstar p L y ≤ 4*P.rho)
    (z : R3) (hz : ‖z‖ = 1) :
    let x := packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z
    ∃ rho : R3 × R3 → ℝ,
      ContDiffAt ℝ ∞ rho (x,y) ∧ rho (x,y) = 0 ∧
      (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ∧
      ∀ᶠ w in 𝓝 z,
        rho (packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) w,y) =
          (⟪w,w⟫_ℝ-1)/2 := by
  intro x
  let r : R3 → ℝ := referenceRadius delta Rstar p L
  let r0 := r y
  let q : ReferenceNormalParameters := (lam,(y,r0))
  let f := referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi
  let E : R3 → R3 := fun w => referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r0),w))
  have hrpos : 0 < r0 := referenceRadius_pos delta Rstar p L y hd hR
  have hrabs : |r0| ≤ 4*P.rho := by rw [abs_of_pos hrpos];exact hr
  have hz2 : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  obtain ⟨psi,hpsi,hval,hright,hleft⟩ := exists_packet_joint_local_normalizedEndpoint_inverse
    S L P lam hlam y hy r0 hrabs z hz2
  let rho := implicitNormalSpherePhase psi lam r
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  have hi := contDiff_referenceFramedNormalizedEndpointIntegral S.g1 S.g1_admissible L P.Phi hTheta
  have hE : ContDiff ℝ ∞ E := hi.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hf : ContinuousAt f (q,z) :=
    (contDiff_referenceFramedNormalizedEndpointIntegralJoint S.g1 S.g1_admissible L P.Phi hTheta).continuous.continuousAt
  have hnear : ∀ᶠ w in 𝓝 z, psi (q,E w) = w := normal_inverse_eq_near f q z psi hf hleft
  have hphys (w : R3) : packetEndpoint S L P lam y r0 w = y+r0 • E w :=
    referenceFramedPhysicalEndpoint_eq_center_add_radius_integral_on_domain S.g1
      S.g1_admissible L P.y0 P.Phi P.B hEnd (lam,((y,r0),w))
      ⟨hlam,(P.centers_room y hy).2⟩
  have hArg (w : R3) : normalizedPhaseArgument lam r (y+r0 • E w,y) = (q,E w) := by
    simp only [normalizedPhaseArgument,Prod.fst,Prod.snd,add_sub_cancel_left]
    change ((lam,(y,r0)),r0⁻¹ • (r0 • E w)) = (q,E w)
    rw [smul_smul,inv_mul_cancel₀ hrpos.ne',one_smul]
  have hx : x = y+r0 • E z := hphys z
  have hArgx : normalizedPhaseArgument lam r (x,y) = (q,E z) := by rw [hx];exact hArg z
  have hpc : ContDiffAt ℝ ∞ psi (normalizedPhaseArgument lam r (x,y)) := by
    rw [hArgx]
    exact hpsi
  have hRho : ContDiffAt ℝ ∞ rho (x,y) :=
    contDiffAt_implicitNormalSpherePhase psi lam r x y
      (contDiff_referenceRadius_actual delta Rstar p L hd hR).contDiffAt hrpos.ne' hpc
  have hzero : rho (x,y) = 0 := by
    change (⟪psi (normalizedPhaseArgument lam r (x,y)),psi (normalizedPhaseArgument lam r (x,y))⟫_ℝ-1)/2 = 0
    rw [hArgx,hval,real_inner_self_eq_norm_sq,hz]
    norm_num
  have hlocal : ∀ᶠ w in 𝓝 z, rho (y+r0 • E w,y) = (⟪w,w⟫_ℝ-1)/2 := by
    filter_upwards [hnear] with w hw
    change (⟪psi (normalizedPhaseArgument lam r (y+r0 • E w,y)),
      psi (normalizedPhaseArgument lam r (y+r0 • E w,y))⟫_ℝ-1)/2 = _
    rw [hArg,hw]
  refine ⟨rho,hRho,hzero,
    first_partial_ne_zero_of_radial_sphere_identity rho E r0 x y z hRho
      (hE.differentiable (by simp) z) hx hz hlocal,?_⟩
  filter_upwards [hlocal] with w hw
  rw [hphys]
  exact hw

/-- A single OPEN C-infinity room for the ACTUAL native reference-radius sphere and its first covector. -/
theorem exists_packet_referenceRadius_open_first_phase
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hR : 0 < Rstar)
    (y : R3) (hy : y ∈ P.centers)
    (hr : referenceRadius delta Rstar p L y ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let x := packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) z
    ∃ U : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
      IsOpen U ∧ (x,y) ∈ U ∧ ContDiffOn ℝ ∞ rho U ∧ rho (x,y) = 0 ∧
      (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ∧
      (∀ᶠ w in 𝓝 z,
        rho (packetEndpoint S L P lam y (referenceRadius delta Rstar p L y) w,y) =
          (⟪w,w⟫_ℝ-1)/2) ∧
      ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 (referenceRadius delta Rstar p L b.1) b.2,b.1) =
          (⟪b.2,b.2⟫_ℝ-1)/2 := by
  intro x
  let r : R3 → ℝ := referenceRadius delta Rstar p L
  let r0 := r y
  let q : ReferenceNormalParameters := (lam,(y,r0))
  let f := referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi
  let E : R3 → R3 := fun w => referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r0),w))
  have hrpos : 0 < r0 := referenceRadius_pos delta Rstar p L y hd hR
  have hrabs : |r0| ≤ 4*P.rho := by rw [abs_of_pos hrpos];exact hr
  have hz2 : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  obtain ⟨psi,V,hV,hbaseV,hpsi,hval,hright,hleft⟩ := exists_packet_open_smooth_normalizedEndpoint_inverse
    S L P lam hlam y hy r0 hrabs z hz2
  let Arg := normalizedPhaseArgument lam r
  let U : Set (R3 × R3) := Arg ⁻¹' V
  let rho := implicitNormalSpherePhase psi lam r
  have hrCD : ContDiff ℝ ∞ r := contDiff_referenceRadius_actual delta Rstar p L hd hR
  have hr2 : ContDiff ℝ ∞ (fun v : R3 × R3 => r v.2) := hrCD.comp contDiff_snd
  have hi2 : ContDiff ℝ ∞ (fun v : R3 × R3 => (r v.2)⁻¹) :=
    hr2.inv (fun v => (referenceRadius_pos delta Rstar p L v.2 hd hR).ne')
  have hArg : ContDiff ℝ ∞ Arg :=
    (contDiff_const.prodMk (contDiff_snd.prodMk hr2)).prodMk
      (hi2.smul (contDiff_fst.sub contDiff_snd))
  have hU : IsOpen U := hV.preimage hArg.continuous
  have hZ : ContDiffOn ℝ ∞ (fun v => psi (Arg v)) U :=
    hpsi.comp hArg.contDiffOn (fun v hv => hv)
  have hRhoOn : ContDiffOn ℝ ∞ rho U :=
    ((hZ.inner ℝ hZ).sub contDiffOn_const).div_const 2
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hE : ContDiff ℝ ∞ E :=
    (contDiff_referenceFramedNormalizedEndpointIntegral S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hnear : ∀ᶠ w in 𝓝 z, psi (q,E w) = w := by
    have ht : Tendsto (fun w : R3 => (q,w)) (𝓝 z) (𝓝 (q,z)) :=
      (continuousAt_const.prodMk continuousAt_id).tendsto
    filter_upwards [ht.eventually hleft] with w hw
    exact hw
  have hphys (w : R3) : packetEndpoint S L P lam y r0 w = y+r0 • E w :=
    referenceFramedPhysicalEndpoint_eq_center_add_radius_integral_on_domain S.g1
      S.g1_admissible L P.y0 P.Phi P.B hEnd (lam,((y,r0),w)) ⟨hlam,(P.centers_room y hy).2⟩
  have hArgE (w : R3) : Arg (y+r0 • E w,y) = (q,E w) := by
    simp only [Arg,normalizedPhaseArgument,Prod.fst,Prod.snd,add_sub_cancel_left]
    change ((lam,(y,r0)),r0⁻¹ • (r0 • E w)) = (q,E w)
    rw [smul_smul,inv_mul_cancel₀ hrpos.ne',one_smul]
  have hx : x = y+r0 • E z := hphys z
  have hArgx : Arg (x,y) = (q,E z) := by rw [hx];exact hArgE z
  have hxU : (x,y) ∈ U := by change Arg (x,y) ∈ V;rw [hArgx];exact hbaseV
  have hRhoAt : ContDiffAt ℝ ∞ rho (x,y) := hRhoOn.contDiffAt (hU.mem_nhds hxU)
  have hzero : rho (x,y) = 0 := by
    change (⟪psi (Arg (x,y)),psi (Arg (x,y))⟫_ℝ-1)/2 = 0
    rw [hArgx,hval,real_inner_self_eq_norm_sq,hz]
    norm_num
  have hlocal : ∀ᶠ w in 𝓝 z, rho (y+r0 • E w,y) = (⟪w,w⟫_ℝ-1)/2 := by
    filter_upwards [hnear] with w hw
    change (⟪psi (Arg (y+r0 • E w,y)),psi (Arg (y+r0 • E w,y))⟫_ℝ-1)/2 = _
    rw [hArgE,hw]
  refine ⟨U,rho,hU,hxU,hRhoOn,hzero,
    first_partial_ne_zero_of_radial_sphere_identity rho E r0 x y z hRhoAt
      (hE.differentiable (by simp) z) hx hz hlocal,?_,?_⟩
  · filter_upwards [hlocal] with w hw
    rw [hphys]
    exact hw
  · have ht : Tendsto (fun b : R3 × R3 => ((lam,(b.1,r b.1)),b.2))
        (𝓝 (y,z)) (𝓝 (q,z)) := by
      have hc : Continuous (fun b : R3 × R3 => ((lam,(b.1,r b.1)),b.2)) := by fun_prop
      exact hc.continuousAt.tendsto
    have hcent : ∀ᶠ b : R3 × R3 in 𝓝 (y,z), b.1 ∈ P.centers :=
      continuousAt_fst.eventually (P.centers_open.mem_nhds hy)
    filter_upwards [ht.eventually hleft,hcent] with b hb hcenter
    let Eb := referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((b.1,r b.1),b.2))
    have hphysb : packetEndpoint S L P lam b.1 (r b.1) b.2 = b.1+r b.1 • Eb :=
      referenceFramedPhysicalEndpoint_eq_center_add_radius_integral_on_domain S.g1
        S.g1_admissible L P.y0 P.Phi P.B hEnd (lam,((b.1,r b.1),b.2))
        ⟨hlam,(P.centers_room b.1 hcenter).2⟩
    have hArgb : Arg (packetEndpoint S L P lam b.1 (r b.1) b.2,b.1) =
        ((lam,(b.1,r b.1)),Eb) := by
      simp only [Arg,normalizedPhaseArgument,Prod.fst,Prod.snd]
      rw [hphysb,add_sub_cancel_left,smul_smul,
        inv_mul_cancel₀ (referenceRadius_pos delta Rstar p L b.1 hd hR).ne',one_smul]
    change (⟪psi (Arg (packetEndpoint S L P lam b.1 (r b.1) b.2,b.1)),
      psi (Arg (packetEndpoint S L P lam b.1 (r b.1) b.2,b.1))⟫_ℝ-1)/2 = _
    change psi ((lam,(b.1,r b.1)),Eb) = b.2 at hb
    rw [hArgb,hb]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
