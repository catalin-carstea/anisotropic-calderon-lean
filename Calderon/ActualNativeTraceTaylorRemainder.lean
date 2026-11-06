import Calderon.LocalUniformTaylorRemainder

/-! Genuine Taylor remainders of the SAME coarse native trace families.
All equalities and bounds are in BallSobolev 2 →L SphereL2. -/
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

def referenceNativeRadialTraceSecondRemainder
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ)
    (y : R3) (r : ℝ) : BallSobolev 2 →L[ℝ] SphereL2 :=
  secondTaylorRemainder (fun t : ℝ =>
    referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,t)) r

def referenceNativeCoordinateTraceSecondRemainder
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ)
    (i : Fin 3) (y : R3) (r : ℝ) : BallSobolev 2 →L[ℝ] SphereL2 :=
  secondTaylorRemainder (fun t : ℝ =>
    referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,t)) r

theorem exists_reference_commonRadius_nativeTraceTaylorRemainder
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∃ C_rad : ℝ, ∃ C_coord : Fin 3 → ℝ,
        0 ≤ C_rad ∧ (∀ i, 0 ≤ C_coord i) ∧
        ∀ y ∈ closedBall y0 ρ, ∀ r : ℝ, |r| ≤ δ →
          referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,r) =
            referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,0) +
            r • radialFirstDerivative
              (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) (y,0) +
            r^2 • referenceNativeRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r ∧
          ‖referenceNativeRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r‖ ≤ C_rad/2 ∧
          ∀ i : Fin 3,
            referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,r) =
              referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,0) +
              r • radialFirstDerivative
                (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) (y,0) +
              r^2 • referenceNativeCoordinateTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i y r ∧
            ‖referenceNativeCoordinateTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i y r‖ ≤ C_coord i/2 := by
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_nativeTraceOperatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0
  refine ⟨δ,hδ,hδρ,?_⟩
  intro q hq
  obtain ⟨C0,Ci,hC0,hCi,hActual⟩ := hRoom q hq 0
  obtain ⟨Cr,hCr,hRad⟩ := exists_compact_local_uniform_secondTaylorRemainder
    (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q)
    (closedBall y0 ρ) (isCompact_closedBall _ _) δ hδ.le
    (fun p hp => (hActual p hp).2.1)
  have hCoord (i : Fin 3) : ∃ Cj : ℝ, 0 ≤ Cj ∧
      ∀ y ∈ closedBall y0 ρ, ∀ r : ℝ, |r| ≤ δ →
        referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,r) =
          referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,0) +
          r • radialFirstDerivative
            (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) (y,0) +
          r^2 • referenceNativeCoordinateTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i y r ∧
        ‖referenceNativeCoordinateTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i y r‖ ≤ Cj/2 := by
    exact exists_compact_local_uniform_secondTaylorRemainder
      (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i)
      (closedBall y0 ρ) (isCompact_closedBall _ _) δ hδ.le
      (fun p hp => (hActual p hp).2.2.1 i)
  choose Cj hCj hCoordBound using hCoord
  refine ⟨Cr,Cj,hCr,hCj,?_⟩
  intro y hy r hr
  exact ⟨(hRad y hy r hr).1,(hRad y hy r hr).2,fun i => hCoordBound i y hy r hr⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
