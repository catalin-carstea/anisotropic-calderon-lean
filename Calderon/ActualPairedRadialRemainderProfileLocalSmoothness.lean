import Calderon.ActualPairedRadialRemainderThreeJetRoom

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance referencePairedProfileOpenRoomHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedProfileOpenRoomNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedProfileOpenRoomHighOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referencePairedProfileOpenRoomLowOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

local instance referencePairedProfileOpenRoomHighIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referencePairedProfileOpenRoomLowIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))

attribute [local irreducible] harmonicSphereSubspace referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceRadialEndpointInvertibleLocus secondTaylorRemainder

theorem exists_referencePairedRadialRemainder_profile_open_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let SegΩ : Set (ℝ × (R3 × ℝ)) :=
      {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
    let Sh : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let Sl : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z =>
      referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let Th : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let Tl : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    IsOpen SegΩ ∧ ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ⊆ Ω ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
      ∀ s : ℝ, |s| ≤ 1 →
      let U : Set R3 := {x | (q,(x,s*R x)) ∈ SegΩ}
      IsOpen U ∧ (∀ x ∈ closedBall y0 ρ, |R x| ≤ d → x ∈ U) ∧
      ∀ power : ℕ,
        ContDiffOn ℝ ∞ (fun x => (s*R x)^power • Sh (q,(x,s*R x))) U ∧
        ContDiffOn ℝ ∞ (fun x => (s*R x)^power • Sl (q,(x,s*R x))) U ∧
        ContDiffOn ℝ ∞ (fun x => (s*R x)^power • Th (q,(x,s*R x))) U ∧
        ContDiffOn ℝ ∞ (fun x => (s*R x)^power • Tl (q,(x,s*R x))) U := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_PROFILE_OPEN_ROOM_BODY"
    out.flush
  intro Ω SegΩ Sh Sl Th Tl
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSegOpen : IsOpen SegΩ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hL : Continuous (fun v : (ℝ × (R3 × ℝ)) × ℝ =>
        (v.1.1,(v.1.2.1,v.2*v.1.2.2))) :=
      continuous_fst.fst.prodMk
        (continuous_fst.snd.fst.prodMk (continuous_snd.mul continuous_fst.snd.snd))
    have hTubeOpen : IsOpen {v : (ℝ × (R3 × ℝ)) × ℝ |
        (v.1.1,(v.1.2.1,v.2*v.1.2.2)) ∈ Ω} := hΩ.preimage hL
    change ∀ᶠ z' in 𝓝 z, ∀ θ ∈ Icc (0 : ℝ) 1,
      (z'.1,(z'.2.1,θ*z'.2.2)) ∈ Ω
    apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).eventually_forall_of_forall_eventually
    intro θ hθ
    exact hTubeOpen.mem_nhds (hz θ hθ)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_PROFILE_OPEN_ROOM_SEGMENT_OPEN"
    out.flush
  have hSmooth (z : ℝ × (R3 × ℝ)) (hz : z ∈ SegΩ) :=
    contDiffAt_referencePairedRadialSecondRemainder_product_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
      z.1 z.2.1 z.2.2 hz
  have hSh : ContDiffOn ℝ ∞ Sh SegΩ := by
    intro z hz
    exact ((hSmooth z hz).1.fst).contDiffWithinAt
  have hSl : ContDiffOn ℝ ∞ Sl SegΩ := by
    intro z hz
    exact ((hSmooth z hz).1.snd).contDiffWithinAt
  have hTh : ContDiffOn ℝ ∞ Th SegΩ := by
    intro z hz
    exact ((hSmooth z hz).2.fst).contDiffWithinAt
  have hTl : ContDiffOn ℝ ∞ Tl SegΩ := by
    intro z hz
    exact ((hSmooth z hz).2.snd).contDiffWithinAt
  let raw := Classical.choice (exists_referencePairedRadialRemainderThreeJetRoom
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg)
  refine ⟨hSegOpen,raw.radius,raw.radius_pos,raw.radius_le,raw.radius_le_one,
    raw.endpointRoom,?_⟩
  intro q hq R hR s hs U
  let χ : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,s*R x))
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_const.prodMk (contDiff_id.prodMk (contDiff_const.mul hR))
  have hU : IsOpen U := hSegOpen.preimage hχ.continuous
  have hMap : MapsTo χ U SegΩ := fun x hx => hx
  have hShU : ContDiffOn ℝ ∞ (fun x => Sh (χ x)) U := hSh.comp hχ.contDiffOn hMap
  have hSlU : ContDiffOn ℝ ∞ (fun x => Sl (χ x)) U := hSl.comp hχ.contDiffOn hMap
  have hThU : ContDiffOn ℝ ∞ (fun x => Th (χ x)) U := hTh.comp hχ.contDiffOn hMap
  have hTlU : ContDiffOn ℝ ∞ (fun x => Tl (χ x)) U := hTl.comp hχ.contDiffOn hMap
  refine ⟨hU,?_,?_⟩
  · intro x hx hRx θ hθ
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hsr : |s*R x| ≤ raw.radius := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans
        (by simpa only [one_mul] using hRx)
    have hθr : |θ*(s*R x)| ≤ raw.radius := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)).trans
        (by simpa only [one_mul] using hsr)
    exact raw.endpointRoom ⟨hq,hx,abs_le.mp hθr⟩
  · intro power
    have hPow : ContDiff ℝ ∞ (fun x => (s*R x)^power) := (contDiff_const.mul hR).pow power
    run_tac do
      let out ← IO.getStdout
      out.putStrLn "PAIRED_PROFILE_OPEN_ROOM_PROFILE_LOCAL_READY"
      out.flush
    exact ⟨hPow.contDiffOn.smul hShU,hPow.contDiffOn.smul hSlU,
      hPow.contDiffOn.smul hThU,hPow.contDiffOn.smul hTlU⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePairedRadialRemainder_profile_open_room
