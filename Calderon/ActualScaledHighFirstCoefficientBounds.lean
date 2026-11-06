import Calderon.ActualJointHighHorizontal
import Calderon.ActualHighAdjointMovingBoundaryFamily
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  MetricOperator NormalCoordinatesFrame
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

theorem exists_compact_referenceScaledHighFirst_coefficients_bound
    (hreg : FixedDirichletRegularity) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K)
    (hRoom : ∀ t ∈ K, t ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hInv : ∀ t ∈ K, ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (t.1,(t.2,x.val))).IsInvertible) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t ∈ K, ∀ i : Fin 3,
      ‖referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t i‖ ≤ M ∧
      ‖referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i‖ ≤ M ∧
      ‖referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t‖ ≤ M ∧
      ‖referenceHighHorizontalAngularL g L t.1 t.2.1 i‖ ≤ M ∧
      ‖referenceMetricGramFrame g L (t.1,t.2.1) i‖ ≤ M ∧
      ‖conformalReferenceGramFrameOperatorJoint g L (t.1,t.2.1) (coordinateVector i)‖ ≤ M := by
  let T (i : Fin 3) (t : ℝ × (R3 × ℝ)) := (referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t i,(referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i,(referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t,(referenceHighHorizontalAngularL g L t.1 t.2.1 i,(referenceMetricGramFrame g L (t.1,t.2.1) i,conformalReferenceGramFrameOperatorJoint g L (t.1,t.2.1) (coordinateVector i))))))
  have hQ (i : Fin 3) : ContinuousOn (fun t => referenceHighAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t i) K := by
    intro t ht
    exact (contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg t i (hRoom t ht)).continuousAt.continuousWithinAt
  have hJ (i : Fin 3) : ContinuousOn (fun t => referenceHighAdjointJacobiBoundaryCorrectionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t i) K := by
    intro t ht
    exact (contDiffAt_referenceHighAdjointJacobiBoundaryCorrectionFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg t i (hInv t ht) (hRoom t ht)).continuousAt.continuousWithinAt
  have hA : ContinuousOn (fun t => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 t) K := by
    intro t ht
    exact ((contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hRoom t ht))).continuousAt.continuousWithinAt
  have hProj : ContDiff ℝ ∞ (fun t : ℝ × (R3 × ℝ) => (t.1,t.2.1)) :=
    contDiff_fst.prodMk contDiff_snd.fst
  have hOmega (i : Fin 3) : ContinuousOn (fun t : ℝ × (R3 × ℝ) => referenceHighHorizontalAngularL g L t.1 t.2.1 i) K :=
    ((contDiff_referenceHighHorizontalAngularL_joint g hg L i).comp hProj).continuous.continuousOn
  have he (i : Fin 3) : ContinuousOn (fun t : ℝ × (R3 × ℝ) => referenceMetricGramFrame g L (t.1,t.2.1) i) K :=
    ((contDiff_referenceMetricGramFrame g hg L i).comp hProj).continuous.continuousOn
  have hv (i : Fin 3) : ContinuousOn (fun t : ℝ × (R3 × ℝ) => conformalReferenceGramFrameOperatorJoint g L (t.1,t.2.1) (coordinateVector i)) K :=
    (((contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp hProj).clm_apply
      contDiff_const).continuous.continuousOn
  have hT (i : Fin 3) : ContinuousOn (T i) K :=
    (hQ i).prodMk ((hJ i).prodMk (hA.prodMk ((hOmega i).prodMk ((he i).prodMk (hv i)))))
  have hBounds : ∀ i : Fin 3, ∃ M : ℝ, ∀ t ∈ K, ‖T i t‖ ≤ M := by
    intro i
    exact hK.exists_bound_of_continuousOn (hT i)
  choose M hBound using hBounds
  obtain ⟨C0,hC0⟩ := (Set.finite_range M).bddAbove
  refine ⟨max C0 1,le_max_right _ _,?_⟩
  intro t ht i
  have h : ‖T i t‖ ≤ max C0 1 :=
    (hBound i t ht).trans ((hC0 ⟨i,rfl⟩).trans (le_max_left _ _))
  simpa only [T,Prod.norm_def,max_le_iff] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
