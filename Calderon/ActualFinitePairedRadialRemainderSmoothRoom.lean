import Calderon.ActualFinitePairedRadialRemainderGraphRoom
import Calderon.ActualFinitePhysicalDomainCommonRoom

/-! The original paired graph room and high strong-inverse tube determine one exact common radius. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

structure ReferenceFinitePairedRadialRemainderSmoothRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) where
  graphRoom : ReferenceFinitePairedRadialRemainderSectionRoom
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  strongRadius : ℝ
  strongRadius_pos : 0 < strongRadius
  strongRadius_le : strongRadius ≤ ρ
  commonRadius : ℝ
  commonRadius_eq : commonRadius = min graphRoom.primalRadius
    (min graphRoom.adjointRadius strongRadius)
  commonRadius_pos : 0 < commonRadius
  commonRadius_le_primal : commonRadius ≤ graphRoom.primalRadius
  commonRadius_le_adjoint : commonRadius ≤ graphRoom.adjointRadius
  commonRadius_le_strong : commonRadius ≤ strongRadius
  commonRadius_le : commonRadius ≤ ρ
  strongInverse : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ
      (closedBall y0 ρ ×ˢ Icc (-strongRadius) strongRadius),
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible

theorem exists_referenceFinitePairedRadialRemainderSmoothRoom
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    Nonempty (ReferenceFinitePairedRadialRemainderSmoothRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-SMOOTH-ROOM BODY_ENTER"
    out.flush
  let room := Classical.choice
    (exists_referenceFinitePairedRadialRemainderSectionRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-SMOOTH-ROOM GRAPH_ROOM_READY"
    out.flush
  obtain ⟨lam,Lam,dRoom,hlam,hdRoom,hdRoomρ,hRoom⟩ :=
    exists_reference_commonRadius_finitePhysicalDomain_room
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-SMOOTH-ROOM STRONG_PARENT_READY"
    out.flush
  let δ : ℝ := min room.primalRadius (min room.adjointRadius dRoom)
  have hδ : 0 < δ :=
    lt_min room.primalRadius_pos (lt_min room.adjointRadius_pos hdRoom)
  have hδP : δ ≤ room.primalRadius := min_le_left _ _
  have hδA : δ ≤ room.adjointRadius :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδRoom : δ ≤ dRoom :=
    (min_le_right _ _).trans (min_le_right _ _)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-PAIRED-SMOOTH-ROOM ASSEMBLY_ENTER"
    out.flush
  exact ⟨{
    graphRoom := room
    strongRadius := dRoom
    strongRadius_pos := hdRoom
    strongRadius_le := hdRoomρ
    commonRadius := δ
    commonRadius_eq := rfl
    commonRadius_pos := hδ
    commonRadius_le_primal := hδP
    commonRadius_le_adjoint := hδA
    commonRadius_le_strong := hδRoom
    commonRadius_le := hδP.trans room.primalRadius_le
    strongInverse := fun p hp => (hRoom p hp).2.2.2.1.1
  }⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceFinitePairedRadialRemainderSmoothRoom
