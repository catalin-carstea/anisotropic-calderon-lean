import Calderon.ActualReferencePairedProductRadialRemainderLocalSmoothness
import Calderon.CompactInverseDerivativeBounds

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-actual-paired-fixed-three-jet-room-v042.md. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

local instance referencePairedRawJetRoomHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedRawJetRoomNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referencePairedRawJetRoomHighOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referencePairedRawJetRoomLowOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

attribute [local irreducible] harmonicSphereSubspace referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceRadialEndpointInvertibleLocus secondTaylorRemainder

structure ReferencePairedRadialRemainderThreeJetRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le : radius ≤ ρ
  radius_le_one : radius ≤ 1
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  endpointRoom : (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-radius) radius)) ⊆
    referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  primalPairSmooth : ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-radius) radius),
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
        (referenceSharpRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2,
         referenceLowerRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2)) point
  adjointPairSmooth : ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-radius) radius),
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
        (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2,
         secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2)) point
  primalPairBounds : ∀ k : ℕ, k ≤ 3 →
    ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-radius) radius),
      ‖iteratedFDeriv ℝ k (fun z : ℝ × (R3 × ℝ) =>
        (referenceSharpRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2,
         referenceLowerRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2)) point‖ ≤ bound
  adjointPairBounds : ∀ k : ℕ, k ≤ 3 →
    ∀ point ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-radius) radius),
      ‖iteratedFDeriv ℝ k (fun z : ℝ × (R3 × ℝ) =>
        (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2,
         secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2)) point‖ ≤ bound

theorem exists_referencePairedRadialRemainderThreeJetRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    Nonempty (ReferencePairedRadialRemainderThreeJetRoom
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_RAW_THREE_JET_ROOM BODY_ENTER"
    out.flush
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Ktube : ℝ → Set (ℝ × (R3 × ℝ)) := fun d =>
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
  obtain ⟨delta0,hdelta0,hdelta0ρ,hRoom0⟩ :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let d : ℝ := min delta0 1
  have hd : 0 < d := lt_min hdelta0 (by norm_num)
  have hdDelta : d ≤ delta0 := min_le_left _ _
  have hdρ : d ≤ ρ := hdDelta.trans hdelta0ρ
  have hd1 : d ≤ 1 := min_le_right _ _
  have hRoom : Ktube d ⊆ Ω := by
    intro point hp
    exact hRoom0 ⟨hp.1,hp.2.1,
      (Icc_subset_Icc (neg_le_neg hdDelta) hdDelta) hp.2.2⟩
  have hSegment (point : ℝ × (R3 × ℝ)) (hp : point ∈ Ktube d) :
      ∀ θ ∈ Icc (0 : ℝ) 1, (point.1,(point.2.1,θ*point.2.2)) ∈ Ω := by
    intro θ hθ
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hr : |point.2.2| ≤ d := abs_le.mpr hp.2.2
    have hθr : |θ*point.2.2| ≤ d := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)).trans
        (by simpa only [one_mul] using hr)
    exact hRoom ⟨hp.1,hp.2.1,abs_le.mp hθr⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_RAW_THREE_JET_ROOM ROOM_READY"
    out.flush
  let S : (ℝ × (R3 × ℝ)) →
      ((SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) ×
       (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) :=
    (fun z : ℝ × (R3 × ℝ) =>
        (referenceSharpRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2,
         referenceLowerRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2))
  let T : (ℝ × (R3 × ℝ)) →
      ((SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) ×
       (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) :=
    (fun z : ℝ × (R3 × ℝ) =>
        (secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2,
         secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
           g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2))
  have hSmooth (point : ℝ × (R3 × ℝ)) (hp : point ∈ Ktube d) :
      ContDiffAt ℝ ∞ S point ∧ ContDiffAt ℝ ∞ T point :=
    contDiffAt_referencePairedRadialSecondRemainder_product_families_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
      point.1 point.2.1 point.2.2 (hSegment point hp)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_RAW_THREE_JET_ROOM PAIRED_SMOOTH_READY"
    out.flush
  have hCompact : IsCompact (Ktube d) :=
    isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  obtain ⟨Ms,hMs,hBs⟩ := exists_compact_iteratedFDeriv_bound
    S (Ktube d) hCompact (fun point hp => (hSmooth point hp).1) 3
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_RAW_THREE_JET_ROOM PRIMAL_COMPACT_READY"
    out.flush
  obtain ⟨Mt,hMt,hBt⟩ := exists_compact_iteratedFDeriv_bound
    T (Ktube d) hCompact (fun point hp => (hSmooth point hp).2) 3
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_RAW_THREE_JET_ROOM ADJOINT_COMPACT_READY"
    out.flush
  let M : ℝ := max Ms Mt
  have hM : 0 ≤ M := hMs.trans (le_max_left _ _)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PAIRED_RAW_THREE_JET_ROOM ASSEMBLY_READY"
    out.flush
  exact ⟨{ radius := d
           radius_pos := hd
           radius_le := hdρ
           radius_le_one := hd1
           bound := M
           bound_nonneg := hM
           endpointRoom := hRoom
           primalPairSmooth := fun point hp => (hSmooth point hp).1
           adjointPairSmooth := fun point hp => (hSmooth point hp).2
           primalPairBounds := fun k hk point hp =>
             (hBs k hk point hp).trans (le_max_left Ms Mt)
           adjointPairBounds := fun k hk point hp =>
             (hBt k hk point hp).trans (le_max_right Ms Mt) }⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
