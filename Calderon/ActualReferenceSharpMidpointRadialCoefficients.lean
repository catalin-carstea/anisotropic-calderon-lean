import Calderon.ActualReferenceSharpMidpointRadialCoefficientCore
import Calderon.SharpRadialCoefficientOperators

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceSharpMidpointRadialTrace_zero_eq_degree
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) = sphereSobolevDegreeL := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k u
  have h := referenceSharpMidpointRadialTrace_zero_single
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy k u
  rw [map_smul,sphereSobolevZeroEquiv_harmonic_subtype] at h
  exact h.trans (sphereSobolevDegreeL_single k u).symm

theorem radialFirstDerivative_referenceSharpMidpointRadialTrace_eq_firstDrift
    (hzero : SmoothBoundaryZeroClosure)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0) =
      sphereSobolevFirstRadialDriftL hF hO hD (referenceCenterDrift g L q y) := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k u
  exact (radialFirstDerivative_referenceSharpMidpointRadialTrace_single
    g L y0 Φ B ε C ρ H a w hData hzero hcalc hF hO hD τ0 hreg q hq y hy k u).trans
    (sphereSobolevFirstRadialDriftL_single hF hO hD (referenceCenterDrift g L q y) k u).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
