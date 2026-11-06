import Calderon.ActualNativeTraceFirstOperatorDerivative
import Calderon.NativeReferenceHarmonicBoundary

/-! Actual SAME coarse native trace Taylor identities on harmonic polynomial
data. Second remainders retain their genuine CLM integral definitions and
uniform bulk-H2 to sphere-L2 bounds. No boundary order or Psi claim. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

theorem smoothRadialSphere_smoothPolynomialData_of_isHomogeneous
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous k) :
    smoothRadialSphere (smoothPolynomialData p) = (k : ℝ) • polynomialSphere p := by
  ext x
  change fderiv ℝ (fun z : R3 => eval (polynomialCoordinateMap z) p) x.val x.val =
    (k : ℝ) * eval (fun i => x.val i) p
  rw [fderiv_polynomialEval_apply]
  have hEuler := congrArg (eval (fun i => x.val i)) hp.sum_X_mul_pderiv
  simpa only [map_sum,map_mul,eval_X,map_natCast,map_nsmul,nsmul_eq_mul] using hEuler

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceNativeRadialTraceOperatorFamily_harmonic_polynomial_zero
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : harmonicHomogeneous k) :
    referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,0)
      (polynomialBallSobolev 2 p) = (k : ℝ) • polynomialSphereL2 p := by
  rw [referenceNativeRadialTraceOperatorFamily,ContinuousLinearMap.comp_apply,
    referenceHarmonicLiftFamily_polynomial_zero_eq
      g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy p p.property.2,
    outwardRadialTraceL_polynomialBallSobolev,
    smoothRadialSphere_smoothPolynomialData_of_isHomogeneous k p p.property.1]
  exact map_smul (ContinuousMap.toLp 2 sphereProbability ℝ) (k : ℝ) (polynomialSphere p)

theorem referenceNativeCoordinateTraceOperatorFamily_harmonic_polynomial_zero
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : harmonicHomogeneous k) (i : Fin 3) :
    referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,0)
      (polynomialBallSobolev 2 p) = polynomialSphereL2 (pderiv i p) := by
  rw [referenceNativeCoordinateTraceOperatorFamily,ContinuousLinearMap.comp_apply,
    referenceHarmonicLiftFamily_polynomial_zero_eq
      g L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy p p.property.2]
  change strongCoordinateTraceL hcalc τ0 i (smoothBallSobolev 2 (smoothPolynomialData p)) = _
  rw [strongCoordinateTraceL_smooth,smoothCoordinateDerivative_smoothPolynomialData]
  rfl

theorem radialFirstDerivative_referenceNativeRadialTrace_harmonic_polynomial
    (hzero : SmoothBoundaryZeroClosure)
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
    exact radialFirstDerivative_referenceNativeRadialTrace_positive
      g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg τ0 hF hO hD q hq y hy m p

theorem radialFirstDerivative_referenceNativeCoordinateTrace_harmonic_polynomial
    (hzero : SmoothBoundaryZeroClosure)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : harmonicHomogeneous k) (i : Fin 3) :
    radialFirstDerivative
      (referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i) (y,0)
      (polynomialBallSobolev 2 p) =
        coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L q y) i (polynomialSphereL2 p) := by
  cases k with
  | zero =>
    exact radialFirstDerivative_referenceNativeCoordinateTrace_constant
      g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 hF hO hD q hq y hy p i
  | succ m =>
    exact radialFirstDerivative_referenceNativeCoordinateTrace_positive
      g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg τ0 hF hO hD q hq y hy m p i

theorem exists_reference_commonRadius_harmonic_polynomial_trace_taylor
    (hzero : SmoothBoundaryZeroClosure)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∃ C_rad : ℝ, ∃ C_coord : Fin 3 → ℝ,
        0 ≤ C_rad ∧ (∀ i, 0 ≤ C_coord i) ∧
        ∀ y ∈ closedBall y0 ρ, ∀ r : ℝ, |r| ≤ δ → ∀ k : ℕ, ∀ p : harmonicHomogeneous k,
          referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,r)
            (polynomialBallSobolev 2 p) =
              (k : ℝ) • polynomialSphereL2 p +
              r • radialDriftTraceL hF hO hD (referenceCenterDrift g L q y) (polynomialSphereL2 p) +
              r^2 • referenceNativeRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r
                (polynomialBallSobolev 2 p) ∧
          ‖referenceNativeRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r
            (polynomialBallSobolev 2 p)‖ ≤ (C_rad/2) * ‖polynomialBallSobolev 2 p‖ ∧
          ∀ i : Fin 3,
            referenceNativeCoordinateTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i (y,r)
              (polynomialBallSobolev 2 p) =
                polynomialSphereL2 (pderiv i p) +
                r • coordinateRadialDriftTraceL hF hO hD (referenceCenterDrift g L q y) i (polynomialSphereL2 p) +
                r^2 • referenceNativeCoordinateTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i y r
                  (polynomialBallSobolev 2 p) ∧
            ‖referenceNativeCoordinateTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i y r
              (polynomialBallSobolev 2 p)‖ ≤ (C_coord i/2) * ‖polynomialBallSobolev 2 p‖ := by
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_nativeTraceTaylorRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0
  refine ⟨δ,hδ,hδρ,?_⟩
  intro q hq
  obtain ⟨C_rad,C_coord,hCrad,hCcoord,hTaylor⟩ := hRoom q hq
  refine ⟨C_rad,C_coord,hCrad,hCcoord,?_⟩
  intro y hy r hr k p
  have hyNorm : ‖y-y0‖ ≤ ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hT := hTaylor y hy r hr
  have hRad := congrArg (fun A : BallSobolev 2 →L[ℝ] SphereL2 => A (polynomialBallSobolev 2 p)) hT.1
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hRad
  rw [referenceNativeRadialTraceOperatorFamily_harmonic_polynomial_zero
      g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 q hq y hyNorm k p,
    radialFirstDerivative_referenceNativeRadialTrace_harmonic_polynomial
      g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg τ0 hF hO hD q hq y hyNorm k p] at hRad
  refine ⟨hRad,?_,?_⟩
  · exact ((referenceNativeRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q y r).le_opNorm (polynomialBallSobolev 2 p)).trans
      (mul_le_mul_of_nonneg_right hT.2.1 (norm_nonneg _))
  · intro i
    have hCoord := congrArg (fun A : BallSobolev 2 →L[ℝ] SphereL2 => A (polynomialBallSobolev 2 p))
      (hT.2.2 i).1
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] at hCoord
    rw [referenceNativeCoordinateTraceOperatorFamily_harmonic_polynomial_zero
        g L y0 Φ B ε C ρ H a w hData hcalc hreg τ0 q hq y hyNorm k p i,
      radialFirstDerivative_referenceNativeCoordinateTrace_harmonic_polynomial
        g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg τ0 hF hO hD q hq y hyNorm k p i] at hCoord
    refine ⟨hCoord,?_⟩
    exact ((referenceNativeCoordinateTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q i y r).le_opNorm (polynomialBallSobolev 2 p)).trans
      (mul_le_mul_of_nonneg_right (hT.2.2 i).2 (norm_nonneg _))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothRadialSphere_smoothPolynomialData_of_isHomogeneous
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeRadialTraceOperatorFamily_harmonic_polynomial_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeCoordinateTraceOperatorFamily_harmonic_polynomial_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceNativeRadialTrace_harmonic_polynomial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radialFirstDerivative_referenceNativeCoordinateTrace_harmonic_polynomial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_harmonic_polynomial_trace_taylor
