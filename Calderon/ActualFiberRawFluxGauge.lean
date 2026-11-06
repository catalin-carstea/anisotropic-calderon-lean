import Calderon.ActualFiberPositiveCoefficient

/-! EXPANSION.json precedes the exact raw-coefficient/conformal-gauge bridge. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hg hData

theorem neg_coordinateFluxDivergence_referenceNormalizedCoefficient_eq
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (u : SmoothData) :
    -coordinateFluxDivergence (fun x => matrixOperatorMap
      (referencePhysicalNormalizedPrincipalCoefficient g L Φ H (q,(y,r)) x)
      (gradient u.1 x : R3)) z =
      Real.exp (L*referenceRescaledDepth g L Φ (q,(y,r)) z) *
        referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) u.1 z := by
  have hPos : ∀ x : R3, (H ((q,(y,r)),x)).PosDef := by
    rcases hData.1 with ⟨_,_,_,_,_,_,_,hPositive,_,_,_,_,_,_,_⟩
    exact fun x => hPositive ((q,(y,r)),x)
  have hFlux : metricDivergenceFlux
      (conformalMatrix (fun x => H ((q,(y,r)),x))
        (fun x => L*referenceRescaledDepth g L Φ (q,(y,r)) x)) u.1 =
      (fun x => matrixOperatorMap
        (referencePhysicalNormalizedPrincipalCoefficient g L Φ H (q,(y,r)) x)
        (gradient u.1 x : R3)) := by
    funext x
    simp only [metricDivergenceFlux,principalCoefficient_conformalMatrix _ _ hPos]
    rfl
  have h := referenceRescaledConformalPositiveExpression_eq
    g L Φ H w hg y0 B ε C ρ a hData q hq y hy r hr z hz u.1 u.2
  change -coordinateFluxDivergence (metricDivergenceFlux
      (conformalMatrix (fun x => H ((q,(y,r)),x))
        (fun x => L*referenceRescaledDepth g L Φ (q,(y,r)) x)) u.1) z = _ at h
  rw [hFlux] at h
  exact h

theorem coordinateFluxDivergence_referenceNormalizedCoefficient_zero_iff
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (u : SmoothData) :
    coordinateFluxDivergence (fun x => matrixOperatorMap
      (referencePhysicalNormalizedPrincipalCoefficient g L Φ H (q,(y,r)) x)
      (gradient u.1 x : R3)) z = 0 ↔
      referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) u.1 z = 0 := by
  have h := neg_coordinateFluxDivergence_referenceNormalizedCoefficient_eq
    g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr z hz u
  constructor
  · intro hZero
    rw [hZero,neg_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Real.exp_pos _).ne'
  · intro hZero
    rw [hZero,mul_zero] at h
    exact neg_eq_zero.mp h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.neg_coordinateFluxDivergence_referenceNormalizedCoefficient_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coordinateFluxDivergence_referenceNormalizedCoefficient_zero_iff
