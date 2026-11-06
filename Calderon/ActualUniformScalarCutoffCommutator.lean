import Calderon.ActualUniformRadiusScaledFirstAction
import Calderon.ActualScalarCutoffCommutatorPointBound
import Calderon.ActualScalarCutoffJointCoefficients
import Calderon.ActualDensityPrincipalFrameCoefficientBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
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

theorem exists_uniform_referenceDensityScalarCutoffCommutator_bound
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (chi : R3 → ℝ) (hchi : ContDiff ℝ ∞ chi) (C0 : ℝ) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ q ∈ Icc (0:ℝ) 1,
      ∀ (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2:ℝ)) (y : R3),
      ‖y-y0‖ ≤ 4*ρ → DifferentiableAt ℝ R y → R y ≠ 0 → |R y| ≤ 4*ρ →
      ‖fderiv ℝ R y‖ ≤ 1 → ‖u y‖ ≤ C0 → ‖fderiv ℝ u y‖ ≤ C0 →
      ‖referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi u y‖ ≤ Cstar := by
  obtain ⟨B0,hB0,hScaled⟩ := exists_uniform_radiusScaled_referenceHighDensityFirstAction_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg C0
  obtain ⟨Mc,hMc,hCutoff⟩ := exists_compact_referenceDensity_cutoff_scalar_coefficients_bound
    g g2 hg hg2 L chi hchi (closedBall y0 (4*ρ)) (isCompact_closedBall _ _)
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let M := max Mc (max 3 (max (4*ρ) (max (‖I‖*C0) 1)))
  have hMcM : Mc ≤ M := le_max_left _ _
  have h3M : 3 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hrM : 4*ρ ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hIM : ‖I‖*C0 ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hM : 1 ≤ M := hMc.trans hMcM
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hB00 : 0 ≤ B0 := zero_le_one.trans hB0
  let Cstar := 9*(M*(M*B0+M*B0+M*M*M))+3*(M*M*M*M)+1
  have hCstar : 1 ≤ Cstar := by
    have hP : 0 ≤ 9*(M*(M*B0+M*B0+M*M*M))+3*(M*M*M*M) := by positivity
    dsimp [Cstar]
    linarith only [hP]
  refine ⟨Cstar,hCstar,?_⟩
  intro q hq R u y hy hR hr hrAbs hDR hu hDu
  have hyK : y ∈ closedBall y0 (4*ρ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hIu : ‖I (u y)‖ ≤ M :=
    (I.le_opNorm (u y)).trans ((mul_le_mul_of_nonneg_left hu (norm_nonneg I)).trans hIM)
  have hPrincipal (i j : Fin 3) : |referenceDensityPrincipalFrameCoefficient g g2 L q y i j| ≤ M :=
    (abs_referenceDensityPrincipalFrameCoefficient_le_three g g2 hg hg2 L q y i j).trans h3M
  have hFirst (i : Fin 3) : |referenceFrameScalarDerivative g L q chi y i| ≤ M :=
    ((hCutoff q hq y hyK i 0).1).trans hMcM
  have hHessian (i j : Fin 3) : |referenceFrameScalarHessian g L q chi y i j| ≤ M :=
    ((hCutoff q hq y hyK i j).2.1).trans hMcM
  have hDrift (i : Fin 3) : |normalizedSecondDriftFrameJoint g g2 L i (q,y)| ≤ M :=
    ((hCutoff q hq y hyK i 0).2.2).trans hMcM
  have hAction (i : Fin 3) := hScaled q hq R u y hy hR hr hrAbs hDR hu hDu i
  have hBound := norm_referenceDensityScalarCutoffCommutator_le_of_point_bounds
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi u y M B0 hM hB00 (hrAbs.trans hrM) hIu
      hPrincipal hFirst hHessian hDrift hAction
  change ‖referenceDensityScalarCutoffCommutator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R chi u y‖ ≤ 9*(M*(M*B0+M*B0+M*M*M))+3*(M*M*M*M)+1
  linarith only [hBound]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
