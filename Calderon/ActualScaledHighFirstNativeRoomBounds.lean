import Calderon.ActualScaledHighFirstCoefficientBounds
import Calderon.ActualHighAdjointMovingBoundaryFamily
import Calderon.ActualReferenceGaugeRadialInverse
import Calderon.ActualGlobalNativeDensityOperatorPackage
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

theorem exists_actual_room_referenceScaledHighFirst_coefficients_bound
    (hreg : FixedDirichletRegularity) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0:ℝ) 1,
      ∀ y : R3, ‖y-y0‖ ≤ 4*ρ → ∀ r : ℝ, |r| ≤ 4*ρ → ∀ i : Fin 3,
      ‖referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r)) i‖ ≤ M ∧
      ‖referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (q,(y,r)) i‖ ≤ M ∧
      ‖referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,r))‖ ≤ M ∧
      ‖referenceHighHorizontalAngularL g L q y i‖ ≤ M ∧
      ‖referenceMetricGramFrame g L (q,y) i‖ ≤ M ∧
      ‖conformalReferenceGramFrameOperatorJoint g L (q,y) (NormalCoordinatesFrame.coordinateVector i)‖ ≤ M := by
  let K : Set (ℝ × (R3 × ℝ)) := Icc (0:ℝ) 1 ×ˢ
    (closedBall y0 (4*ρ) ×ˢ Icc (-4*ρ) (4*ρ))
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hRoom : ∀ t ∈ K, t ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    rintro ⟨q,y,r⟩ ⟨hq,hy,hr⟩
    have hc : ‖y-y0‖ ≤ 4*ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have ha : |r| ≤ 4*ρ := abs_le.mpr ⟨by linarith [hr.1],hr.2⟩
    exact referenceRadialEndpointInvertibleLocus_mem_on_actual_room
      g hg L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q hq y hc r ha
  have hInv : ∀ t ∈ K, ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,(t.2,x.val))).IsInvertible := by
    rintro ⟨q,y,r⟩ ⟨hq,hy,hr⟩ x
    have hc : ‖y-y0‖ ≤ 4*ρ := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have ha : |r| ≤ 4*ρ := abs_le.mpr ⟨by linarith [hr.1],hr.2⟩
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall
      g hg L y0 Φ B ε C ρ H a w hData q hq y hc r ha x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  obtain ⟨M,hM,hBound⟩ := exists_compact_referenceScaledHighFirst_coefficients_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg K hK hRoom hInv
  refine ⟨M,hM,?_⟩
  intro q hq y hy r hr i
  have hp : (q,(y,r)) ∈ K := by
    refine ⟨hq,?_,?_⟩
    · simpa only [mem_closedBall,dist_eq_norm] using hy
    · exact ⟨by linarith [(abs_le.mp hr).1],(abs_le.mp hr).2⟩
  exact hBound (q,(y,r)) hp i

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
