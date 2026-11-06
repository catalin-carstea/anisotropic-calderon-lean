import Calderon.ActualNativeMovingAdjointMixedJGraph

/-! Upfront: actual-native-mixed-J-dictionary-author-oct16-v001/EXPANSION-realization-timeout-exact-three-way-split-v003.md.
Actual ordered mixed zero/first expression, same finite-J graph and bound. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic AngularShiftGraph
  ActualNormalizedSecondMetricDrift

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  sphereSobolevAngularCoordinateTransposeL referenceNativeMovingAdjointParametricCorrection
  referenceNativeMovingAdjointParametricJ referenceDensityPrincipalFrameCoefficient
  normalizedSecondDriftFrameJoint sphereSobolevInclusionL

attribute [local irreducible] referenceNativeMovingAdjointHighMixedCorrection

lemma exists_referenceNativeMovingAdjointHighMixedCorrection_uniform_bound
    (g2 : MatrixField) (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ hreg : FixedDirichletRegularity,
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ →
      ∀ ell : R3 →L[ℝ] ℝ, ‖ell‖ ≤ 1 → ∀ u : SphereSobolev (3/2 : ℝ),
        ‖sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (referenceNativeMovingAdjointHighMixedCorrection g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 q y ell u)‖ ≤
          CJ * ‖sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) u‖ := by
  obtain ⟨CJ,hCJpos,hCJ⟩ := exists_referenceNativeMovingAdjointParametricJ_uniform_bound
    hF hO hD g g2 hg hg2 L (closedBall y0 ρ) (isCompact_closedBall _ _)
  refine ⟨CJ,hCJpos,?_⟩
  intro hreg q hq y hy ell hell u
  have hK : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hGraph := referenceNativeMovingAdjointHighMixedCorrection_inclusion
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 g2 hreg q hq y hy ell u
  let T := referenceNativeMovingAdjointParametricJ hF hO hD g g2 L ((q,y),ell)
  let U := sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) u
  calc
    _ = ‖T U‖ := congrArg norm hGraph
    _ ≤ ‖T‖ * ‖U‖ := T.le_opNorm U
    _ ≤ CJ * ‖U‖ := mul_le_mul_of_nonneg_right (hCJ q hq y hK ell hell) (norm_nonneg U)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceNativeMovingAdjointHighMixedCorrection_uniform_bound
