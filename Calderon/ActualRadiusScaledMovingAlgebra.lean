import Calderon.ActualDensityScalarCutoff
import Calderon.ActualHighAdjointMovingBoundaryFamilyDefinition

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift MetricOperator NormalCoordinatesFrame

private lemma scale_moving_three_terms
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r c : ℝ) (a b d : V) (hr : r ≠ 0) :
    r • (r⁻¹ • a + r • b + c • d) = a + r^2 • b + (r*c) • d := by
  simp only [smul_add,smul_smul,mul_inv_cancel₀ hr,one_smul,pow_two]

def radiusScaledMovingCombination {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r t : ℝ) (Q J A : V) : V := Q + r^2 • J + t • A

private lemma scale_moving_to_combination
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r c : ℝ) (Q J A : V) (hr : r ≠ 0) :
    r • (r⁻¹ • Q + r • J + c • A) = radiusScaledMovingCombination r (r*c) Q J A :=
  scale_moving_three_terms r c Q J A hr

theorem radiusScaledMovingCombination_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (r t : ℝ) (Q J A : V →L[ℝ] W) (u : V) :
    radiusScaledMovingCombination r t Q J A u = Q u + r^2 • J u + t • A u := by
  simp only [radiusScaledMovingCombination,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]

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
  conformalReferenceGramFrameOperatorJoint referenceMetricGramFrame

theorem referenceRadiusHorizontalLogDerivative_mul_radius
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0) :
    R y * referenceRadiusHorizontalLogDerivative g L q R y i =
      fderiv ℝ R y (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i)) := by
  unfold referenceRadiusHorizontalLogDerivative
  rw [fderiv.log hR hr]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [←mul_assoc,mul_inv_cancel₀ hr,one_mul]

theorem radius_smul_referenceHighAdjointMovingBoundaryActionFamily_algebra
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hR : DifferentiableAt ℝ R y) (hr : R y ≠ 0) :
    let Q := referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i
    let J := referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i
    let A := referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))
    R y • referenceHighAdjointMovingBoundaryActionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,y) i =
      radiusScaledMovingCombination (R y)
        (R y*referenceRadiusHorizontalLogDerivative g L q R y i) Q J A := by
  extract_lets Q J A
  delta referenceHighAdjointMovingBoundaryActionFamily
  exact scale_moving_to_combination (R y) (referenceRadiusHorizontalLogDerivative g L q R y i) Q J A hr

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
