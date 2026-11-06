import Calderon.ActualNativeFirstVariationRadialFactor
import Calderon.ActualNativeTraceFirstOperatorDerivative

/-! SAME actual coarse derivative, using the proved radialFactor curve derivative. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma radialFirstDerivative_referenceNativeRadialTrace_positive_radialFactor
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (m : ℕ) (p : harmonicHomogeneous (m+1)) :
    radialFirstDerivative
      (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) (y,0)
      (polynomialBallSobolev 2 p) =
        radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (polynomialSphereL2 p) := by
  have hi := referenceStrongDriftFamily_zero_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy
  have hs := contDiffAt_referenceNativeRadialTraceOperatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,0) hi
  have hd : HasDerivAt (fun r : ℝ =>
      referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,r))
      (radialFirstDerivative
        (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) (y,0)) 0 := by
    have hc : HasDerivAt (fun r : ℝ => (y,r)) (0,1) 0 :=
      (hasDerivAt_const 0 y).prodMk (hasDerivAt_id 0)
    simpa only [Function.comp_def,radialFirstDerivative] using
      (hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hc
  have he := hd.clm_apply (hasDerivAt_const (0 : ℝ) (polynomialBallSobolev 2 p))
  have ho := hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_firstCorrection_radialFactor
    g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 hF hO hD q hq y hy m p
  simp only [map_zero,add_zero,zero_add] at he
  exact he.unique ho

lemma radialFirstDerivative_referenceNativeRadialTrace_harmonic_polynomial_radialFactor
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : harmonicHomogeneous k) :
    radialFirstDerivative
      (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q) (y,0)
      (polynomialBallSobolev 2 p) =
        radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (polynomialSphereL2 p) := by
  cases k with
  | zero =>
    exact radialFirstDerivative_referenceNativeRadialTrace_constant
      g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 hF hO hD q hq y hy p
  | succ m =>
    exact radialFirstDerivative_referenceNativeRadialTrace_positive_radialFactor
      g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 hF hO hD q hq y hy m p

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceNativeRadialTrace_positive_radialFactor
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceNativeRadialTrace_harmonic_polynomial_radialFactor
