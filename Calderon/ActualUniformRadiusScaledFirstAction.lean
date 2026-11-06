import Calderon.ActualScaledHighFirstNativeRoomBounds
import Calderon.ActualHighAdjointMovingBoundaryFamily
import Calderon.ActualReferenceGaugeRadialInverse
import Calderon.ActualGlobalNativeDensityOperatorPackage
import Calderon.ActualRadiusScaledFirstActionNative
import Calderon.RadiusScaledFirstActionNormBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  MetricOperator NormalCoordinatesFrame MetricVolume NativeSmoothSharpTraceCompletion MixedKernelConstructionTask
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
attribute [local irreducible] referenceHighAdjointCoordinateBoundaryFamily
  referenceHighAdjointJacobiBoundaryCorrectionFamily referenceAdjointThreeHalfRadialFamily
  referenceHighHorizontalAngularL referenceMetricGramFrame conformalReferenceGramFrameOperatorJoint

attribute [local irreducible] referenceHighDensityFirstAction referenceHighHorizontalAction sphereSobolevInclusionL

theorem exists_uniform_radiusScaled_referenceHighDensityFirstAction_bound
    (hreg : FixedDirichletRegularity) (C0 : ℝ) :
    ∃ B0 : ℝ, 1 ≤ B0 ∧ ∀ q ∈ Icc (0:ℝ) 1,
      ∀ (R : R3 → ℝ) (u : R3 → SphereSobolev (3/2:ℝ)) (y : R3),
      ‖y-y0‖ ≤ 4*ρ → DifferentiableAt ℝ R y → R y ≠ 0 → |R y| ≤ 4*ρ →
      ‖fderiv ℝ R y‖ ≤ 1 → ‖u y‖ ≤ C0 → ‖fderiv ℝ u y‖ ≤ C0 →
      ∀ i : Fin 3, ‖R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i‖ ≤ B0 := by
  obtain ⟨G,hG,hBounds⟩ := exists_actual_room_referenceScaledHighFirst_coefficients_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let M := max G (max C0 (max (4*ρ) 1))
  have hGM : G ≤ M := le_max_left _ _
  have hCM : C0 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hrM : 4*ρ ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hM : 1 ≤ M := hG.trans hGM
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let B0 := M*(‖I‖*M*M+M*M)+M*M+M^2*M*M+M*M*M+1
  have hB0 : 1 ≤ B0 := by
    have hP : 0 ≤ M*(‖I‖*M*M+M*M)+M*M+M^2*M*M+M*M*M := by positivity
    dsimp [B0]
    linarith only [hP]
  refine ⟨B0,hB0,?_⟩
  intro q hq R u y hy hR hr hrAbs hDR hu hDu i
  obtain ⟨hQ,hJ,hA,hOmega,he,hv⟩ := hBounds q hq y hy (R y) hrAbs i
  have hGeneric := norm_radiusScaled_first_action_le
    I (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y)) i) (referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,R y)) i) (referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))) (referenceHighHorizontalAngularL g L q y i)
    (fderiv ℝ u y) (fderiv ℝ R y) (R y) (u y)
    (referenceMetricGramFrame g L (q,y) i) (conformalReferenceGramFrameOperatorJoint g L (q,y) (NormalCoordinatesFrame.coordinateVector i)) M
    hM (hrAbs.trans hrM) (hu.trans hCM) (hDu.trans hCM) hDR
    (hQ.trans hGM) (hJ.trans hGM) (hA.trans hGM)
    (hOmega.trans hGM) (he.trans hGM) (hv.trans hGM)
  have hIdentity := radius_smul_referenceHighDensityFirstAction_eq_inverseFree
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i hR hr
  have hBound : ‖R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i‖ ≤ M*(‖I‖*M*M+M*M)+M*M+M^2*M*M+M*M*M := by
    calc
      _ = _ := congrArg (fun z : SphereSobolev (1/2:ℝ) => ‖z‖) hIdentity
      _ ≤ _ := by simpa only [referenceHighHorizontalAction] using hGeneric
  change ‖R y • referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R u y i‖ ≤ M*(‖I‖*M*M+M*M)+M*M+M^2*M*M+M*M*M+1
  linarith only [hBound]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
