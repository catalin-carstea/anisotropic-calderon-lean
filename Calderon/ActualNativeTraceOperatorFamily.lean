import Calderon.ActualReferenceStrongRoom
import Calderon.NativeCoordinateTraceVariation

/-! The SAME actual native coarse trace CLM families. The input remains
BallSobolev 2, not a completed boundary Sobolev space. These roots supply
ambient operator-norm smoothness through zero on the actual signed inverse
room, with finite compact jets. No boundary order or Psi claim is made. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceNativeRadialTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ)
    (p : R3 × ℝ) : BallSobolev 2 →L[ℝ] SphereL2 :=
  (outwardRadialTraceL hcalc τ0).comp
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p)

def referenceNativeCoordinateTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ)
    (i : Fin 3) (p : R3 × ℝ) : BallSobolev 2 →L[ℝ] SphereL2 :=
  (strongCoordinateTraceL hcalc τ0 i).comp
    (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p)

theorem contDiffAt_referenceHarmonicLiftFamily_zero_order
    (hcalc : FixedSobolevCalculus) (q : ℝ) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q) p := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  have hOrdinary := contDiff_referenceOrdinaryStrongDriftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 0 q
  have hStrong : ContDiff ℝ ∞
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q) := by
    exact hOrdinary.clm_comp contDiff_const
  exact contDiffAt_guardedHarmonicLiftFamily
    (strongDirichletSubmodule 0).toSubmodule.subtypeL
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q) hStrong
    (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q)
    hOrdinary p hi

theorem contDiffAt_referenceNativeRadialTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) p := by
  exact contDiffAt_const.clm_comp
    (contDiffAt_referenceHarmonicLiftFamily_zero_order
      g L y0 Φ B ε C ρ H a w hData hcalc q p hi)

theorem contDiffAt_referenceNativeCoordinateTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ)
    (i : Fin 3) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) p := by
  exact contDiffAt_const.clm_comp
    (contDiffAt_referenceHarmonicLiftFamily_zero_order
      g L y0 Φ B ε C ρ H a w hData hcalc q p hi)

theorem exists_reference_commonRadius_nativeTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ N : ℕ,
        ∃ C_rad : ℝ, ∃ C_coord : Fin 3 → ℝ,
          0 ≤ C_rad ∧ (∀ i, 0 ≤ C_coord i) ∧
          ∀ p ∈ closedBall y0 ρ ×ˢ Icc (-δ) δ,
            (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible ∧
            ContDiffAt ℝ ∞
              (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) p ∧
            (∀ i, ContDiffAt ℝ ∞
              (referenceNativeCoordinateTraceOperatorFamily
                g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) p) ∧
            ∀ j : ℕ, j ≤ N →
              ‖iteratedFDeriv ℝ j
                (referenceNativeRadialTraceOperatorFamily
                  g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) p‖ ≤ C_rad ∧
              ∀ i, ‖iteratedFDeriv ℝ j
                (referenceNativeCoordinateTraceOperatorFamily
                  g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) p‖ ≤ C_coord i := by
  obtain ⟨lam,Lam,δ,hlam,hδ,hδρ,hRoom⟩ :=
    exists_reference_commonRadius_allOrder_strongDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg
  refine ⟨δ,hδ,hδρ,?_⟩
  intro q hq N
  let K : Set (R3 × ℝ) := closedBall y0 ρ ×ˢ Icc (-δ) δ
  have hK : IsCompact K := (isCompact_closedBall y0 ρ).prod isCompact_Icc
  have hi (p : R3 × ℝ) (hp : p ∈ K) :
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible := by
    have hy : ‖p.1-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.1
    exact (hRoom q hq p.1 hy p.2 (abs_le.mpr hp.2)).2 0
  have hRad (p : R3 × ℝ) (hp : p ∈ K) : ContDiffAt ℝ ∞
      (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) p :=
    contDiffAt_referenceNativeRadialTraceOperatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p (hi p hp)
  have hCoord (i : Fin 3) (p : R3 × ℝ) (hp : p ∈ K) : ContDiffAt ℝ ∞
      (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) p :=
    contDiffAt_referenceNativeCoordinateTraceOperatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i p (hi p hp)
  obtain ⟨C_rad,hCrad,hRadBound⟩ := exists_compact_iteratedFDeriv_bound _ K hK hRad N
  have hCoordBounds (i : Fin 3) :
      ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ K,
        ‖iteratedFDeriv ℝ j
          (referenceNativeCoordinateTraceOperatorFamily
            g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) p‖ ≤ Ci :=
    exists_compact_iteratedFDeriv_bound _ K hK (hCoord i) N
  choose C_coord hCcoord hCoordBound using hCoordBounds
  refine ⟨C_rad,C_coord,hCrad,hCcoord,?_⟩
  intro p hp
  refine ⟨hi p hp,hRad p hp,fun i => hCoord i p hp,?_⟩
  intro j hj
  exact ⟨hRadBound j hj p hp,fun i => hCoordBound i j hj p hp⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHarmonicLiftFamily_zero_order
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceNativeRadialTraceOperatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceNativeCoordinateTraceOperatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_nativeTraceOperatorFamily
