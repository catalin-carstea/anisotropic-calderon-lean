import Calderon.ActualRadiusScaledMovingAlgebra

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift MetricOperator NormalCoordinatesFrame
private lemma prepend_three_terms {V : Type*} [AddCommGroup V]
    (a b c d : V) : a+(b+c+d)=a+b+c+d := by abel

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighDensityFirstAction referenceHighHorizontalAction
  referenceHighAdjointMovingBoundaryActionFamily referenceHighAdjointCoordinateBoundaryFamily
  referenceHighAdjointJacobiBoundaryCorrectionFamily referenceAdjointThreeHalfRadialFamily
  conformalReferenceGramFrameOperatorJoint referenceMetricGramFrame radiusScaledMovingCombination

theorem radius_smul_referenceHighAdjointMovingBoundaryActionFamily
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0) :
    let Q := referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i
    let J := referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i
    let A := referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))
    R y • referenceHighAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i =
      radiusScaledMovingCombination (R y)
        (fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))) Q J A := by
  extract_lets Q J A
  have h0 := radius_smul_referenceHighAdjointMovingBoundaryActionFamily_algebra
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hR hr
  have hLog := referenceRadiusHorizontalLogDerivative_mul_radius g L q R y i hR hr
  have h1 := congrArg (fun t : ℝ => radiusScaledMovingCombination (R y) t Q J A) hLog
  exact h0.trans h1

theorem radius_smul_referenceHighDensityFirstAction_eq_combination
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2:ℝ)) (y : R3) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0) :
    R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i =
      R y • referenceHighHorizontalAction g L q u y i +
      (radiusScaledMovingCombination (R y) (fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)))
      (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i)
      (referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i)
      (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)))) (u y) := by
  have hMove := DFunLike.congr_fun (radius_smul_referenceHighAdjointMovingBoundaryActionFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i hR hr) (u y)
  have hMove' : R y • referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (u y) =
      (radiusScaledMovingCombination (R y) (fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)))
      (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i)
      (referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i)
      (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)))) (u y) := by
    simpa only [ContinuousLinearMap.smul_apply] using hMove
  delta referenceHighDensityFirstAction
  exact (smul_add (R y) (referenceHighHorizontalAction g L q u y i) (referenceHighAdjointMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i (u y))).trans
    (congrArg (fun z : SphereSobolev (1/2:ℝ) => R y • referenceHighHorizontalAction g L q u y i + z) hMove')

theorem radius_smul_referenceHighDensityFirstAction_eq_inverseFree
    (q : ℝ) (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2:ℝ)) (y : R3) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0) :
    R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i =
    R y • referenceHighHorizontalAction g L q u y i +
    referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i (u y) +
    (R y)^2 • referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i (u y) +
    (fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))) • referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) (u y) := by
  have h0 := radius_smul_referenceHighDensityFirstAction_eq_combination
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i hR hr
  have hExpand := radiusScaledMovingCombination_apply (R y) (fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))) (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i) (referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i) (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))) (u y)
  have h1 := congrArg (fun z : SphereSobolev (1/2:ℝ) => R y • referenceHighHorizontalAction g L q u y i + z) hExpand
  exact h0.trans (h1.trans (prepend_three_terms _ _ _ _))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
