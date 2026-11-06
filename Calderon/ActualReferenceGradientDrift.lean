import Calderon.ActualRescaledConformalGauge

/-! Full upfront: day-oct13/actual-gradient-drift-author-oct15-v001/EXPANSION.md.
Exact SAME coefficient and bulk-gradient graph; no gauge/adjoint conclusion assumed. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily.DriftBootstrap

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

theorem gradient_referenceRescaledDepth (p : ℝ × (R3 × ℝ)) (z : R3) :
    gradient (referenceRescaledDepth g L Φ p) z =
      p.2.2 • ((parameterFramedNormalizedEndpointDerivative
        (fun t => (Φ t.1 t.2 1).1) (conformalReferenceGramFrameOperatorJoint g L)
        (p,z)).adjoint
          (gradient conformalReferenceCoordinateDepth
            (parameterFramedScaledEndpoint (fun t => (Φ t.1 t.2 1).1)
              (conformalReferenceGramFrameOperatorJoint g L) (p,z)))) := by
  apply ext_inner_right ℝ
  intro v
  simp only [inner_gradient_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left]
  exact fderiv_referenceRescaledDepth_apply g L Φ H w y0 B ε C ρ a hData p z v

theorem conformalReferenceWeightedFramedDrift_eq_matrix_gradient
    (p : ℝ × (R3 × ℝ)) (z : R3) :
    conformalReferenceWeightedFramedDrift g L Φ H w (p,z) =
      (-L) • matrixOperatorMap (a (p,z)) (gradient (referenceRescaledDepth g L Φ p) z) := by
  have ha : a (p,z) = w (p,z) • (H (p,z))⁻¹ := hData.2.2.2.2.1 (p,z)
  rw [gradient_referenceRescaledDepth g L y0 Φ B ε C ρ H a w hData p z,ha]
  simp only [conformalReferenceWeightedFramedDrift,
    parameterWeightedNormalizedConformalDrift, parameterNormalizedConformalDrift,
    normalizedConformalDrift, normalizedConformalDriftBase, map_smul,
    ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  ring

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.gradient_referenceRescaledDepth
#print axioms OAI.AnisotropicCalderon.ConnectionError.conformalReferenceWeightedFramedDrift_eq_matrix_gradient
