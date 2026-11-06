import Calderon.ActualFiniteHarmonicProductRadialRemainderGraph
import Calderon.ActualFiniteGaugeAdjointRemainderGraph

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-paired-actual-graph-room-record-v016.md.
The nominal room is constructed from both exact actual parent graphs. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

attribute [local irreducible] harmonicSphereSubspace secondTaylorRemainder
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily
  referenceFiniteHarmonicProductHighSecondRemainder referenceFiniteGaugeAdjointSecondRemainder
  nativeThreeHalfCoefficientMulL sphereSobolevInclusionL sphereSobolevPartialSum

local instance actualPairedGraphRoomThreeHalfComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance actualPairedGraphRoomHalfComplete :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance actualPairedGraphRoomHighOperatorComplete : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

local instance actualPairedGraphRoomTraceOperatorComplete : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance

structure ReferenceFinitePairedRadialRemainderSectionRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) where
  primalRadius : ℝ
  adjointRadius : ℝ
  primalRadius_pos : 0 < primalRadius
  primalRadius_le : primalRadius ≤ ρ
  adjointRadius_pos : 0 < adjointRadius
  adjointRadius_le : adjointRadius ≤ ρ
  gauge : ReferenceGaugeNormalReciprocalRoom g L Φ a
    (Icc (0 : ℝ) 1 ×ˢ
      (closedBall y0 ρ ×ˢ Icc (-(2*adjointRadius)) (2*adjointRadius)))
  primalGraph : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
    ∀ r : ℝ, |r| ≤ primalRadius →
    ∀ (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceFiniteHarmonicProductHighSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n Q q y r f) =
      secondTaylorRemainder (fun t : ℝ => referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
            (sphereSobolevPartialSum (3/2 : ℝ) n f))
  adjointGraph : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
    ∀ r : ℝ, |r| ≤ adjointRadius →
    ∀ (n : ℕ) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (3/2 : ℝ)),
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceFiniteGaugeAdjointSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 gauge n Q q y r f) =
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r
          (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
            (sphereSobolevPartialSum (3/2 : ℝ) n f))

theorem exists_referenceFinitePairedRadialRemainderSectionRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    Nonempty (ReferenceFinitePairedRadialRemainderSectionRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-ROOM BODY_ENTER"
    out.flush
  obtain ⟨dP,hdP,hdPρ,hPrimal⟩ :=
    exists_reference_commonRadius_finiteProductHighSecondRemainder_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-ROOM PRIMAL_READY"
    out.flush
  obtain ⟨dA,hdA,hdAρ,G,hAdjoint⟩ :=
    exists_reference_commonRadius_finiteGaugeAdjointSecondRemainder_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0 hKernel
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-ROOM ADJOINT_READY"
    out.flush
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-ROOM ASSEMBLY_ENTER"
    out.flush
  exact ⟨{
    primalRadius := dP
    adjointRadius := dA
    primalRadius_pos := hdP
    primalRadius_le := hdPρ
    adjointRadius_pos := hdA
    adjointRadius_le := hdAρ
    gauge := G
    primalGraph := hPrimal
    adjointGraph := hAdjoint
  }⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceFinitePairedRadialRemainderSectionRoom
