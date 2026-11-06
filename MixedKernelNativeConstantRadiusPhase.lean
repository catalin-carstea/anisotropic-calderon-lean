import MixedKernelImplicitSphereFirstJet
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff InnerProductSpace Topology

/-- Freeze the inverse construction radius using the literal degree-zero radius profile. -/
theorem exists_packet_constant_radius_open_phase
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r0 : ℝ) (hrpos : 0 < r0) (y : R3) (hy : y ∈ P.centers)
    (hr : r0 ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let x := packetEndpoint S L P lam y r0 z
    ∃ U : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
      IsOpen U ∧ (x,y) ∈ U ∧ ContDiffOn ℝ ∞ rho U ∧ rho (x,y) = 0 ∧
      (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ∧
      (∀ᶠ w in 𝓝 z, rho (packetEndpoint S L P lam y r0 w,y) = (⟪w,w⟫_ℝ-1)/2) ∧
      ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 r0 b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2 := by
  simpa only [referenceRadius,pow_zero,mul_one] using
    exists_packet_referenceRadius_open_first_phase S L P lam hlam 1 r0 0
      (by norm_num) hrpos y hy (by simpa only [referenceRadius,pow_zero,mul_one] using hr) z hz

/-- Rescale the actual framed initial velocity, without changing its native geodesic flow. -/
theorem packetEndpoint_radius_rescaling
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (y : R3) (r r0 : ℝ) (hr0 : r0 ≠ 0) (z : R3) :
    packetEndpoint S L P lam y r z =
      packetEndpoint S L P lam y r0 ((r/r0) • z) := by
  let F := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y)
  have hVel : r0 • F ((r/r0) • z) = r • F z := by
    rw [map_smul,smul_smul]
    congr 1
    field_simp
  change (P.Phi lam (y,r • F z) 1).1 = (P.Phi lam (y,r0 • F ((r/r0) • z)) 1).1
  rw [hVel]

/-- A frozen inverse radius gives an energy phase for the SAME actual moving native spheres. -/
theorem exists_packet_moving_phase_from_constant_radius
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r : R3 → ℝ) (hrCD : ContDiff ℝ ∞ r) (y : R3) (hy : y ∈ P.centers)
    (hrpos : 0 < r y) (hr : r y ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let r0 := r y
    let x := packetEndpoint S L P lam y r0 z
    ∃ U : Set (R3 × R3), ∃ rho F : R3 × R3 → ℝ,
      IsOpen U ∧ (x,y) ∈ U ∧ ContDiffOn ℝ ∞ rho U ∧ rho (x,y) = 0 ∧
      ContDiffOn ℝ ∞ F U ∧ F (x,y) = 0 ∧
      (∀ v, F v = r0^2*(rho v+1/2)-(r v.2)^2/2) ∧
      (∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 r0 b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) ∧
      ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        F (packetEndpoint S L P lam b.1 (r b.1) b.2,b.1) =
          (r b.1)^2*(⟪b.2,b.2⟫_ℝ-1)/2 := by
  intro r0 x
  have hr0 : r0 ≠ 0 := hrpos.ne'
  obtain ⟨U,rho,hU,hxy,hRho,hzero,_,_,hfamily⟩ :=
    exists_packet_constant_radius_open_phase S L P lam hlam r0 hrpos y hy hr z hz
  let F : R3 × R3 → ℝ := fun v => r0^2*(rho v+1/2)-(r v.2)^2/2
  have hF : ContDiffOn ℝ ∞ F U := by
    exact ((hRho.add contDiffOn_const).const_smul (r0^2)).sub
      (((hrCD.comp contDiff_snd).contDiffOn.pow 2).div_const 2)
  have hzero' : rho (x,y) = 0 := hzero
  have hFzero : F (x,y) = 0 := by simp only [F,hzero',Prod.snd];dsimp [r0];ring
  have hc : ContinuousAt (fun b : R3 × R3 => (b.1,(r b.1/r0) • b.2)) (y,z) :=
    continuousAt_fst.prodMk (((hrCD.continuous.continuousAt.comp continuousAt_fst).div_const r0).smul continuousAt_snd)
  have ht : Tendsto (fun b : R3 × R3 => (b.1,(r b.1/r0) • b.2))
      (𝓝 (y,z)) (𝓝 (y,z)) := by
    simpa only [r0,div_self hrpos.ne',one_smul] using hc.tendsto
  refine ⟨U,rho,F,hU,hxy,hRho,hzero,hF,hFzero,fun _ => rfl,hfamily,?_⟩
  filter_upwards [ht.eventually hfamily] with b hb
  change rho (packetEndpoint S L P lam b.1 r0 ((r b.1/r0) • b.2),b.1) = _ at hb
  have hEndpoint := packetEndpoint_radius_rescaling S L P lam b.1 (r b.1) r0 hrpos.ne' b.2
  change r0^2*(rho (packetEndpoint S L P lam b.1 (r b.1) b.2,b.1)+1/2)-(r b.1)^2/2 = _
  rw [hEndpoint,hb,real_inner_smul_left,real_inner_smul_right]
  field_simp [hr0]
  <;> ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
