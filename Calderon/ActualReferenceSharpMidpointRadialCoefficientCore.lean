import Calderon.ActualReferenceSharpMidpointRadialDerivativeTransport
import Calderon.SharpRadialHarmonicCoefficientCore

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

theorem referenceSharpMidpointRadialTrace_zero_single
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) (sphereSobolevSingleL 1 k u) =
      sphereSobolevZeroEquiv hO hD ((k : ℝ) • (u : SphereL2)) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have he := referenceSharpMidpointRadialTraceFamily_eq_native_radial_on_high_data
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) hp (sphereSobolevSingleL (3/2 : ℝ) k u)
  rw [sphereSobolevInclusionL_single,harmonicLiftCompletion_sphereSobolevSingle hF hO] at he
  let p : harmonicHomogeneous k :=
    ⟨harmonicPolynomialRepresentativeL hF k u,harmonicPolynomialRepresentative_mem hF k u⟩
  have hz := referenceNativeRadialTraceOperatorFamily_harmonic_polynomial_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 q hq y hy k p
  have hu : polynomialSphereL2 p = (u : SphereL2) :=
    polynomialSphereL2_harmonicPolynomialRepresentative hF k u
  rw [hu] at hz
  exact he.trans (congrArg (sphereSobolevZeroEquiv hO hD) hz)

theorem radialFirstDerivative_referenceSharpMidpointRadialTrace_single
    (hzero : SmoothBoundaryZeroClosure)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (u : harmonicSphereSubspace k) :
    radialFirstDerivative (fun p : R3 × ℝ => referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,p)) (y,0)
      (sphereSobolevSingleL 1 k u) =
      sphereSobolevZeroEquiv hO hD
        (radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (u : SphereL2)) := by
  have hp := referenceRadialEndpointInvertibleLocus_zero_mem g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q hq y hy
  have he := radialFirstDerivative_referenceSharpMidpointRadialTrace_on_high_data
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y hp (sphereSobolevSingleL (3/2 : ℝ) k u)
  rw [sphereSobolevInclusionL_single,harmonicLiftCompletion_sphereSobolevSingle hF hO] at he
  let p : harmonicHomogeneous k :=
    ⟨harmonicPolynomialRepresentativeL hF k u,harmonicPolynomialRepresentative_mem hF k u⟩
  have hz := radialFirstDerivative_referenceNativeRadialTrace_harmonic_polynomial
    g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg τ0 hF hO hD q hq y hy k p
  have hu : polynomialSphereL2 p = (u : SphereL2) :=
    polynomialSphereL2_harmonicPolynomialRepresentative hF k u
  rw [hu] at hz
  exact he.trans (congrArg (sphereSobolevZeroEquiv hO hD) hz)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
