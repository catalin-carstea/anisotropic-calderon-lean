import Calderon.ScalarCutoffCommutatorNormBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualNormalizedSecondMetricDrift
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceDensityScalarCutoffCommutator
  referenceDensityPrincipalFrameCoefficient referenceFrameScalarDerivative referenceFrameScalarHessian
  normalizedSecondDriftFrameJoint referenceHighDensityFirstAction sphereSobolevInclusionL

theorem norm_referenceDensityScalarCutoffCommutator_le_of_point_bounds
    (g2 : MatrixField) (q : ℝ) (R chi : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2:ℝ)) (y : R3) (M B0 : ℝ)
    (hM : 1 ≤ M) (hB0 : 0 ≤ B0) (hr : |R y| ≤ M)
    (hu : ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (u y)‖ ≤ M)
    (hPrincipal : ∀ i j, |referenceDensityPrincipalFrameCoefficient g g2 L q y i j| ≤ M)
    (hFirst : ∀ i, |referenceFrameScalarDerivative g L q chi y i| ≤ M)
    (hHessian : ∀ i j, |referenceFrameScalarHessian g L q chi y i j| ≤ M)
    (hDrift : ∀ i, |normalizedSecondDriftFrameJoint g g2 L i (q,y)| ≤ M)
    (hAction : ∀ i, ‖R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i‖ ≤ B0) :
    ‖referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi u y‖ ≤
      9*(M*(M*B0+M*B0+M*M*M))+3*(M*M*M*M) := by
  delta referenceDensityScalarCutoffCommutator
  exact norm_scalarCutoffCommutator_le (R y)
    (referenceDensityPrincipalFrameCoefficient g g2 L q y) (referenceFrameScalarHessian g L q chi y) (referenceFrameScalarDerivative g L q chi y) (fun i => normalizedSecondDriftFrameJoint g g2 L i (q,y))
    (fun i => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (u y)) M B0
    hM hB0 hr hu hPrincipal hFirst hHessian hDrift hAction

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
