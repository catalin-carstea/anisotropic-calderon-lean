import Calderon.ActualHarmonicLiftZeroDerivative
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

theorem guardedHarmonicLiftFamily_eq_strongHarmonicProjection {P : Type}
    (s : ℕ) (A : P → StrongDirichletSpace s →L[ℝ] BallSobolev s)
    (B : P → BallSobolev (s+2) →L[ℝ] BallSobolev s) (p : P)
    (hi : (A p).IsInvertible)
    (hrest : (B p).comp (strongDirichletSubmodule s).toSubmodule.subtypeL = A p) :
    guardedHarmonicLiftFamily (strongDirichletSubmodule s).toSubmodule.subtypeL A B p =
      strongHarmonicProjectionL s (B p) := by
  classical
  simp only [guardedHarmonicLiftFamily,dif_pos hi]
  unfold harmonicLiftL strongHarmonicProjectionL
  rw [hrest]

theorem strongValueTraceL_guardedHarmonicLiftFamily {P : Type}
    (τ0 : UnitBallValueTrace) (s : ℕ)
    (A : P → StrongDirichletSpace s →L[ℝ] BallSobolev s)
    (B : P → BallSobolev (s+2) →L[ℝ] BallSobolev s) (p : P)
    (hi : (A p).IsInvertible)
    (hrest : (B p).comp (strongDirichletSubmodule s).toSubmodule.subtypeL = A p)
    (E : BallSobolev (s+2)) :
    strongValueTraceL τ0 s
      (guardedHarmonicLiftFamily (strongDirichletSubmodule s).toSubmodule.subtypeL A B p E) =
      strongValueTraceL τ0 s E := by
  rw [guardedHarmonicLiftFamily_eq_strongHarmonicProjection s A B p hi hrest]
  exact strongValueTraceL_strongHarmonicProjection τ0 s (B p) E

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceHarmonicLiftFamily_eq_strongHarmonicProjection
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (z : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z).IsInvertible) :
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z =
      strongHarmonicProjectionL s
        (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z) := by
  exact guardedHarmonicLiftFamily_eq_strongHarmonicProjection s _ _ z hi rfl

theorem strongValueTraceL_referenceHarmonicLiftFamily
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (s : ℕ) (q : ℝ) (z : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z).IsInvertible)
    (E : BallSobolev (s+2)) :
    strongValueTraceL τ0 s
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z E) =
      strongValueTraceL τ0 s E := by
  rw [referenceHarmonicLiftFamily_eq_strongHarmonicProjection
    g L y0 Φ B ε C ρ H a w hData hcalc s q z hi]
  exact strongValueTraceL_strongHarmonicProjection τ0 s _ E

theorem strongValueTraceL_referenceHarmonicLiftFamily_smooth
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (s : ℕ) (q : ℝ) (z : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z).IsInvertible)
    (f : SmoothData) :
    strongValueTraceL τ0 s
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z
        (smoothBallSobolev (s+2) f)) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothSphereValue f) := by
  rw [strongValueTraceL_referenceHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 s q z hi, strongValueTraceL_smooth]

theorem strongValueTraceL_referenceHarmonicLiftFamily_polynomial
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (s : ℕ) (q : ℝ) (z : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z).IsInvertible)
    (p : MvPolynomial (Fin 3) ℝ) :
    strongValueTraceL τ0 s
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z
        (polynomialBallSobolev (s+2) p)) = polynomialSphereL2 p := by
  change strongValueTraceL τ0 s
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q z
        (smoothBallSobolev (s+2) (smoothPolynomialData p))) = _
  rw [strongValueTraceL_referenceHarmonicLiftFamily_smooth
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 s q z hi]
  rfl

theorem referenceHarmonicLiftFamily_polynomial_zero_eq
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (p : MvPolynomial (Fin 3) ℝ) (hΔ : AngularPolynomial.laplacian p = 0) :
    referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)
      (polynomialBallSobolev (s+2) p) = polynomialBallSobolev (s+2) p := by
  have hi := referenceStrongDriftFamily_zero_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq y hy
  rw [referenceHarmonicLiftFamily_eq_strongHarmonicProjection
    g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0) hi]
  apply strongHarmonicProjectionL_eq_self
  rw [referenceOrdinaryStrongDriftFamily_zero_polynomial
    g L y0 Φ B ε C ρ H a w hData hcalc s q hq y hy,hΔ]
  change -(polynomialBallSobolevLinearMap s 0) = 0
  rw [map_zero,neg_zero]

theorem hasDerivAt_referenceValueTraceHarmonicLiftFamily_polynomial_zero
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (τ0 : UnitBallValueTrace) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (p : MvPolynomial (Fin 3) ℝ) (hΔ : AngularPolynomial.laplacian p = 0) :
    HasDerivAt
      (fun r : ℝ => strongValueTraceL τ0 s
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
          (polynomialBallSobolev (s+2) p))) 0 0 := by
  have hd := hasDerivAt_referenceHarmonicLiftFamily_polynomial_zero
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq y hy p hΔ
  have hτ := (strongValueTraceL τ0 s).hasFDerivAt.comp_hasDerivAt 0 hd
  have hz : strongValueTraceL τ0 s
      ((strongDirichletSubmodule s).toSubmodule.subtypeL
        ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)).inverse
          (polynomialBallSobolev s (GreenRadialTrace.driftDerivative
            (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)))) = 0 :=
    strongValueTraceL_subtype τ0 s _
  simpa only [Function.comp_def,hz] using hτ

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
