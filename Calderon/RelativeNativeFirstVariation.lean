import Calderon.ActualHarmonicLiftZeroDerivative
import Calderon.SmoothSobolevBridge

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError

theorem firstOrder_polynomialBallSobolev_driftFirstVariation_mem_w1p0Submodule
    (hzero : SmoothBoundaryZeroClosure) (s k : ℕ) (d : R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    TauCeti.Wkp.firstOrder (s+1)
      (polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
        (polynomialCoordinateMap d) p)) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  rw [firstOrder_polynomialBallSobolev]
  apply hzero (smoothPolynomialData (GreenRadialTrace.driftFirstVariation k
    (polynomialCoordinateMap d) p))
  intro z hz
  exact polynomialEval_driftFirstVariation_zero_on_sphere k d p z hz

theorem polynomialBallSobolev_driftFirstVariation_mem_strongDirichletSubmodule
    (hzero : SmoothBoundaryZeroClosure) (s k : ℕ) (d : R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
      (polynomialCoordinateMap d) p) ∈ strongDirichletSubmodule s := by
  exact (mem_strongDirichletSubmodule s _).mpr
    (firstOrder_polynomialBallSobolev_driftFirstVariation_mem_w1p0Submodule hzero s k d p)

def driftFirstVariationStrongDirichlet
    (hzero : SmoothBoundaryZeroClosure) (s k : ℕ) (d : R3)
    (p : MvPolynomial (Fin 3) ℝ) : StrongDirichletSpace s := ⟨polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
    (polynomialCoordinateMap d) p),
  polynomialBallSobolev_driftFirstVariation_mem_strongDirichletSubmodule hzero s k d p⟩

theorem coe_driftFirstVariationStrongDirichlet
    (hzero : SmoothBoundaryZeroClosure) (s k : ℕ) (d : R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    (driftFirstVariationStrongDirichlet hzero s k d p : BallSobolev (s+2)) =
      polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
        (polynomialCoordinateMap d) p) := rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceStrongDriftFamily_driftFirstVariationStrongDirichlet_forcing
    (hzero : SmoothBoundaryZeroClosure) (hcalc : FixedSobolevCalculus) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : AngularPolynomial.laplacian p = 0) :
    referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)
      (driftFirstVariationStrongDirichlet hzero s k (referenceCenterDrift g L q y) p) =
        polynomialBallSobolev s (GreenRadialTrace.driftDerivative
          (polynomialCoordinateMap (referenceCenterDrift g L q y)) p) := by
  change referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)
    (polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
      (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) = _
  exact referenceOrdinaryStrongDriftFamily_driftFirstVariation_forcing
    g L y0 Φ B ε C ρ H a w hData hcalc s q hq y hy k p hp hΔ

theorem referenceStrongDriftFamily_inverse_driftDerivative_eq_driftFirstVariation
    (hzero : SmoothBoundaryZeroClosure) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : AngularPolynomial.laplacian p = 0) :
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,0)).inverse
      (polynomialBallSobolev s (GreenRadialTrace.driftDerivative
        (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) =
      driftFirstVariationStrongDirichlet hzero s k (referenceCenterDrift g L q y) p := by
  have hi := referenceStrongDriftFamily_zero_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq y hy
  have hforcing := referenceStrongDriftFamily_driftFirstVariationStrongDirichlet_forcing
    g L y0 Φ B ε C ρ H a w hData hzero hcalc s q hq y hy k p hp hΔ
  rw [← hforcing]
  exact hi.inverse_apply_self _

theorem hasDerivAt_referenceHarmonicLiftFamily_driftFirstVariation_zero
    (hzero : SmoothBoundaryZeroClosure) (hcalc : FixedSobolevCalculus)
    (hreg : FixedDirichletRegularity) (s : ℕ)
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
  rw [referenceStrongDriftFamily_inverse_driftDerivative_eq_driftFirstVariation
    g L y0 Φ B ε C ρ H a w hData hzero hcalc hreg s q hq y hy k p hp hΔ] at hd
  change HasDerivAt
    (fun r : ℝ => referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
      (polynomialBallSobolev (s+2) p))
    (polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
      (polynomialCoordinateMap (referenceCenterDrift g L q y)) p)) 0 at hd
  exact hd

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
