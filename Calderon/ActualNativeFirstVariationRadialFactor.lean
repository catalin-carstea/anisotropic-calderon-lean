import Calderon.NativeFirstDriftRadialFactorClosure
import Calderon.ActualNativeRadialFirstVariation
import Calderon.ActualBoundedNativeRadialCorrection

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

/-! Upfront expansion: EXPANSION-native-first-drift-without-general-closure-joint-v001.md. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceStrongDriftFamily_coe_inverse_driftDerivative_radialFactor
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : AngularPolynomial.laplacian p = 0) :
    (strongDirichletSubmodule s).toSubmodule.subtypeL
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)).inverse
        (polynomialBallSobolev s (GreenRadialTrace.driftDerivative
          (polynomialCoordinateMap (referenceCenterDrift g L q y)) p))) =
      polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p) := by
  let U : StrongDirichletSpace s :=
    ⟨polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
      (polynomialCoordinateMap (referenceCenterDrift g L q y)) p),
      polynomialBallSobolev_driftFirstVariation_mem_strongDirichlet_radialFactor
        s k (referenceCenterDrift g L q y) p⟩
  have hforcing : referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0) U =
      polynomialBallSobolev s (GreenRadialTrace.driftDerivative
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p) := by
    change referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)
      (polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) = _
    exact referenceOrdinaryStrongDriftFamily_driftFirstVariation_forcing
      g L y0 Φ B ε C ρ H a w hData hcalc s q hq y hy k p hp hΔ
  have hi := referenceStrongDriftFamily_zero_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq y hy
  have he : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)).inverse
      (polynomialBallSobolev s (GreenRadialTrace.driftDerivative
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) = U := by
    rw [← hforcing]
    exact hi.inverse_apply_self U
  exact congrArg (fun v : StrongDirichletSpace s => (v : BallSobolev (s+2))) he

theorem hasDerivAt_referenceHarmonicLiftFamily_driftFirstVariation_radialFactor
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : AngularPolynomial.laplacian p = 0) :
    HasDerivAt
      (fun r : ℝ => referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
        (polynomialBallSobolev (s+2) p))
      (polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) 0 := by
  have hd := hasDerivAt_referenceHarmonicLiftFamily_polynomial_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq y hy p hΔ
  rw [referenceStrongDriftFamily_coe_inverse_driftDerivative_radialFactor
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq y hy k p hp hΔ] at hd
  exact hd

theorem hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_firstCorrection_radialFactor
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (m : ℕ) (p : harmonicHomogeneous (m+1)) :
    HasDerivAt
      (fun r : ℝ => outwardRadialTraceL hcalc τ0
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      (radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (polynomialSphereL2 p)) 0 := by
  have hd := hasDerivAt_referenceHarmonicLiftFamily_driftFirstVariation_radialFactor
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy (m+1) p p.property.1 p.property.2
  have ht := hasDerivAt_outwardRadialTraceL hcalc τ0 _ _ 0 hd
  rw [outwardRadialTraceL_driftFirstVariation hcalc τ0 (by omega : 1 ≤ m+1)] at ht
  rw [radialDriftTraceL_polynomial hF hO hD (referenceCenterDrift g L q y) m p]
  exact ht

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
