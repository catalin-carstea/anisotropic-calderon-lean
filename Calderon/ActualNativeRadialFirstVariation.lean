import Calderon.RelativeNativeFirstVariation
import Calderon.NativeValueRadialTrace

/-! The full actual joint witness is retained. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

theorem polynomialSphere_driftDerivative_eq_directionalDerivative
    (d : R3) (p : MvPolynomial (Fin 3) ℝ) (x : UnitSphere) :
    polynomialSphere (GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p) x =
      fderiv ℝ (fun z : R3 => eval (polynomialCoordinateMap z) p) x.val d := by
  change eval (fun i => x.val i)
    (GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p) = _
  rw [fderiv_polynomialEval_apply]
  simp only [GreenRadialTrace.driftDerivative, map_sum, map_mul, eval_C,
    polynomialCoordinateMap_apply]

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_polynomial_zero
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (p : MvPolynomial (Fin 3) ℝ) (hΔ : AngularPolynomial.laplacian p = 0) :
    HasDerivAt
      (fun r : ℝ => outwardRadialTraceL hcalc τ0
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      (outwardRadialTraceL hcalc τ0
        ((strongDirichletSubmodule 0).toSubmodule.subtypeL
          ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,0)).inverse
            (polynomialBallSobolev 0 (GreenRadialTrace.driftDerivative
              (polynomialCoordinateMap (referenceCenterDrift g L q y)) p))))) 0 := by
  have hd := hasDerivAt_referenceHarmonicLiftFamily_polynomial_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy p hΔ
  simpa only [Function.comp_def] using
    (outwardRadialTraceL hcalc τ0).hasFDerivAt.comp_hasDerivAt 0 hd

theorem hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_driftFirstVariation_zero
    (hzero : SmoothBoundaryZeroClosure) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : AngularPolynomial.laplacian p = 0) :
    HasDerivAt
      (fun r : ℝ => outwardRadialTraceL hcalc τ0
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      (outwardRadialTraceL hcalc τ0
        (polynomialBallSobolev 2 (GreenRadialTrace.driftFirstVariation k
          (polynomialCoordinateMap (referenceCenterDrift g L q y)) p))) 0 := by
  have hd := hasDerivAt_referenceHarmonicLiftFamily_driftFirstVariation_zero
    g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg 0 q hq y hy k p hp hΔ
  exact hasDerivAt_outwardRadialTraceL hcalc τ0 _ _ 0 hd

theorem hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_zero
    (hzero : SmoothBoundaryZeroClosure) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (hk : 1 ≤ k) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : AngularPolynomial.laplacian p = 0) :
    HasDerivAt
      (fun r : ℝ => outwardRadialTraceL hcalc τ0
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,r)
          (polynomialBallSobolev 2 p)))
      ((-(2 * (k : ℝ) + 1)⁻¹) • polynomialSphereL2
        (GreenRadialTrace.driftDerivative
          (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) 0 := by
  have hd := hasDerivAt_referenceOutwardRadialHarmonicLiftFamily_driftFirstVariation_zero
    g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg τ0 q hq y hy k p hp hΔ
  rw [outwardRadialTraceL_driftFirstVariation hcalc τ0 hk] at hd
  exact hd


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
