import Calderon.ActualReferenceGradientDrift

/-! The exponential gauge: the same positive center-normalized gauge. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator EnergyBridge DirichletFamily.DriftBootstrap

variable (g : MatrixField) (L : ℝ)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)

def referenceExponentialGauge (p : ℝ × (R3 × ℝ)) (z : R3) : ℝ :=
  Real.exp (L * (referenceRescaledDepth g L Φ p z - conformalReferenceCoordinateDepth p.2.1))

theorem referenceExponentialGauge_pos (p : ℝ × (R3 × ℝ)) (z : R3) :
    0 < referenceExponentialGauge g L Φ p z := Real.exp_pos _

variable (hg : IsAdmissibleMetric g) (y0 : R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData

theorem contDiff_referenceRescaledDepth (p : ℝ × (R3 × ℝ)) :
    ContDiff ℝ ∞ (referenceRescaledDepth g L Φ p) := by
  have hTheta : ContDiff ℝ ∞ (fun t : ℝ × (R3 × R3) => (Φ t.1 t.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX := contDiff_parameterFramedScaledEndpoint
    (fun t : ℝ × (R3 × R3) => (Φ t.1 t.2 1).1)
    (conformalReferenceGramFrameOperatorJoint g L) hTheta
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L)
  exact contDiff_conformalReferenceCoordinateDepth.comp
    (hX.comp (contDiff_const.prodMk contDiff_id))

theorem contDiff_referenceExponentialGauge (p : ℝ × (R3 × ℝ)) :
    ContDiff ℝ ∞ (referenceExponentialGauge g L Φ p) := by
  exact (contDiff_const.mul
    ((contDiff_referenceRescaledDepth g L Φ hg y0 B ε C ρ H a w hData p).sub contDiff_const)).exp

theorem gradient_referenceExponentialGauge (p : ℝ × (R3 × ℝ)) (z : R3) :
    gradient (referenceExponentialGauge g L Φ p) z =
      (referenceExponentialGauge g L Φ p z * L) • gradient (referenceRescaledDepth g L Φ p) z := by
  unfold referenceExponentialGauge
  have ht := (contDiff_referenceRescaledDepth g L Φ hg y0 B ε C ρ H a w hData p).differentiable (by simp) z
  have hm :=
    ((ht.hasFDerivAt.sub_const (conformalReferenceCoordinateDepth p.2.1)).const_mul L).exp
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  have hApply := congrArg (fun A : R3 →L[ℝ] ℝ => A v) hm.fderiv
  simpa only [referenceExponentialGauge, ContinuousLinearMap.smul_apply,
    smul_smul, smul_eq_mul, mul_assoc] using hApply

theorem referenceExponentialGauge_weightedDrift_identity
    (p : ℝ × (R3 × ℝ)) (z : R3) :
    referenceExponentialGauge g L Φ p z • conformalReferenceWeightedFramedDrift g L Φ H w (p,z) +
      matrixOperatorMap (a (p,z)) (gradient (referenceExponentialGauge g L Φ p) z) = 0 := by
  rw [conformalReferenceWeightedFramedDrift_eq_matrix_gradient g L y0 Φ B ε C ρ H a w hData p z,
    gradient_referenceExponentialGauge g L Φ hg y0 B ε C ρ H a w hData p z, map_smul]
  simp only [smul_smul]
  rw [← add_smul]
  have hZero : referenceExponentialGauge g L Φ p z * (-L) +
      referenceExponentialGauge g L Φ p z * L = 0 := by ring
  rw [hZero, zero_smul]

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceExponentialGauge
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceExponentialGauge_pos
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceRescaledDepth
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_referenceExponentialGauge
#print axioms OAI.AnisotropicCalderon.ConnectionError.gradient_referenceExponentialGauge
#print axioms OAI.AnisotropicCalderon.ConnectionError.referenceExponentialGauge_weightedDrift_identity
