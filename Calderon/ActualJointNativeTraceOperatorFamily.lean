import Calderon.ActualJointOrdinaryStrongDrift

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

theorem contDiffAt_joint_referenceHarmonicLiftFamily
    (hcalc : FixedSobolevCalculus) (s : ℕ) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
      referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s t.1 t.2) p := by
  letI : CompleteSpace (StrongDirichletSpace s) := instCompleteSpaceStrongDirichletSpace s
  exact contDiffAt_guardedHarmonicLiftFamily
    (strongDirichletSubmodule s).toSubmodule.subtypeL
    (fun t : ℝ × (R3 × ℝ) => referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s t.1 t.2)
    (contDiff_joint_referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s)
    (fun t : ℝ × (R3 × ℝ) => referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s t.1 t.2)
    (contDiff_joint_referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s) p hi

theorem contDiffAt_joint_referenceNativeRadialTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
      referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 t.2) p := by
  exact contDiffAt_const.clm_comp
    (contDiffAt_joint_referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p hi)

theorem contDiffAt_joint_referenceNativeCoordinateTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (i : Fin 3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
      referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 i t.2) p := by
  exact contDiffAt_const.clm_comp
    (contDiffAt_joint_referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p hi)

theorem exists_reference_commonRadius_joint_nativeTraceOperatorFamily
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ N : ℕ,
      ∃ C_rad : ℝ, ∃ C_coord : Fin 3 → ℝ,
        0 ≤ C_rad ∧ (∀ i, 0 ≤ C_coord i) ∧
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
          (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible ∧
          ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
            referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 t.2) p ∧
          (∀ i, ContDiffAt ℝ ∞ (fun t : ℝ × (R3 × ℝ) =>
            referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 i t.2) p) ∧
          ∀ j : ℕ, j ≤ N →
            ‖iteratedFDeriv ℝ j (fun t : ℝ × (R3 × ℝ) =>
              referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 t.2) p‖ ≤ C_rad ∧
            ∀ i, ‖iteratedFDeriv ℝ j (fun t : ℝ × (R3 × ℝ) =>
              referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 i t.2) p‖ ≤ C_coord i := by
  obtain ⟨lam,Lam,δ,hlam,hδ,hδρ,hRoom⟩ :=
    exists_reference_commonRadius_allOrder_strongDrift
      g L y0 Φ B ε C ρ H a w hData hcalc hreg
  refine ⟨δ,hδ,hδρ,?_⟩
  intro N
  let K : Set (ℝ × (R3 × ℝ)) := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hi (p : ℝ × (R3 × ℝ)) (hp : p ∈ K) :
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible := by
    have hy : ‖p.2.1-y0‖ ≤ ρ := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    exact (hRoom p.1 hp.1 p.2.1 hy p.2.2 (abs_le.mpr hp.2.2)).2 0
  have hRad (p : ℝ × (R3 × ℝ)) (hp : p ∈ K) : ContDiffAt ℝ ∞
      (fun t : ℝ × (R3 × ℝ) => referenceNativeRadialTraceOperatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 t.2) p :=
    contDiffAt_joint_referenceNativeRadialTraceOperatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 p (hi p hp)
  have hCoord (i : Fin 3) (p : ℝ × (R3 × ℝ)) (hp : p ∈ K) : ContDiffAt ℝ ∞
      (fun t : ℝ × (R3 × ℝ) => referenceNativeCoordinateTraceOperatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 i t.2) p :=
    contDiffAt_joint_referenceNativeCoordinateTraceOperatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 i p (hi p hp)
  obtain ⟨C_rad,hCrad,hRadBound⟩ := exists_compact_iteratedFDeriv_bound _ K hK hRad N
  have hCoordBounds (i : Fin 3) : ∃ Ci : ℝ, 0 ≤ Ci ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ j (fun t : ℝ × (R3 × ℝ) => referenceNativeCoordinateTraceOperatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc τ0 t.1 i t.2) p‖ ≤ Ci :=
    exists_compact_iteratedFDeriv_bound _ K hK (hCoord i) N
  choose C_coord hCcoord hCoordBound using hCoordBounds
  refine ⟨C_rad,C_coord,hCrad,hCcoord,?_⟩
  intro p hp
  refine ⟨hi p hp,hRad p hp,fun i => hCoord i p hp,?_⟩
  intro j hj
  exact ⟨hRadBound j hj p hp,fun i => hCoordBound i j hj p hp⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
