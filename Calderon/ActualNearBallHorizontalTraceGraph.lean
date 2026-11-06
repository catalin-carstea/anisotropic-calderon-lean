import Calderon.ActualPhysicalHorizontalNativeTrace
import Calderon.ActualMovingBoundaryNativeTraceIdentification
import Calderon.ActualMovingNearBallHarmonicLift

/-! The near-ball harmonic trace graph, derived. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError MetricVolume NativeH2ThreeHalfValueTrace

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referencePhysicalNativeThreeHalfTraceSection
  referencePhysicalPullbackData referenceHighHorizontalAction referenceHighMovingBoundaryAction
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceNormalBoundaryMultiplierFamily referenceNativeMovingRadiusTraceOperator
  referenceFramedNormalizedJacobian referenceFramedPhysicalEndpoint
  referenceHarmonicLiftFamily smoothBallSobolev nativeThreeHalfValueTraceL
  smoothSphereValue smoothRadialSphere metricDivergenceFlux coordinateFluxDivergence

theorem referenceHighHorizontalAction_eq_movingAction_of_physical_harmonic
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ) (hrBound : |R y| ≤ 4*ρ)
    (hyB : (y,0) ∈ B) (hr : R y ≠ 0) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hNormal : (referenceNormalBoundaryMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible)
    (v : SmoothData)
    (hphysical : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) v.1)
        (referenceFramedPhysicalEndpoint g L Φ (q,((y,R y),z))) = 0) :
    referenceHighHorizontalAction g L q
      (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 q R v) y i =
    referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      q R y i hInv
      (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 q R v y) := by
  let E := smoothBallSobolev 2
    (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v)
  have hLift := referenceHarmonicLiftFamily_physical_harmonic_eq_self
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy (R y) hrBound hr v hStrong hphysical
  have hNative := referenceNativeMovingRadiusTraceOperator_physical_smooth
    g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q hq R y hyB hr i hInv v hLift
  have hBoundary := referenceHighMovingBoundaryAction_nativeThreeHalfTrace_eq_coarse
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hKernel q R y i hInv hNormal hStrong hWeak E
  have hHorizontal := referenceHighHorizontalAction_referencePhysicalNativeTrace_coarse
    g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q hq R hR y hyB hr i hInv v
  have hMoving : sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
      (referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        q R y i hInv
        (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
          hcalc hF hO hD τ0 q R v y)) =
      sphereSobolevZeroEquiv hO hD
        ((ContinuousMap.toLp 2 sphereProbability ℝ)
          (referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R y i v)) := by
    simpa only [referencePhysicalNativeThreeHalfTraceSection, E] using
      hBoundary.trans (congrArg (sphereSobolevZeroEquiv hO hD) hNative)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) 0 (by norm_num)
  exact hHorizontal.trans hMoving.symm

theorem exists_referenceHighHorizontalTraceGraph_of_near_ball_harmonic
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ < 4*ρ) (hr : |R y| < 4*ρ) (hr0 : R y ≠ 0)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (hCover : (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,R y),z))) ''
      closedBall (0 : R3) 1 ⊆ S)
    (hphysical : ∀ x ∈ S,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u) x = 0) :
    ∃ (v : SmoothData) (Y : Set R3), HasCompactSupport v.1 ∧ IsOpen Y ∧ y ∈ Y ∧
      ∀ z ∈ Y,
        ContDiffAt ℝ ∞
          (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
            hcalc hF hO hD τ0 q R v) z ∧
        (∀ x : UnitSphere,
          smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) v) x =
            u (referenceFramedPhysicalEndpoint g L Φ (q,((z,R z),x.val)))) ∧
        ∀ hzB : (z,0) ∈ B,
          ∀ hInv : ∀ x : UnitSphere,
            (referenceFramedNormalizedJacobian g L Φ (q,((z,R z),x.val))).IsInvertible,
          ∀ hNormal : (referenceNormalBoundaryMultiplierFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(z,R z))).IsInvertible,
          ∀ hWeak : (referenceWeakDirichletEnergyFamily
            g L y0 Φ B ε C ρ H a w hData hcalc (q,(z,R z))).IsInvertible,
          ∀ i : Fin 3,
            referenceHighHorizontalAction g L q
              (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
                hcalc hF hO hD τ0 q R v) z i =
            referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
              q R z i hInv
              (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
                hcalc hF hO hD τ0 q R v z) := by
  trace "near-ball-graph: body"
  obtain ⟨v,U,hv,hU,hBase,hFamily⟩ := exists_referenceHarmonicLift_family_of_near_ball_harmonic
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy (R y) hr hr0 hi S hS u hu hCover hphysical
  trace "near-ball-graph: compact family"
  let Y : Set R3 := (fun z : R3 => (z,R z)) ⁻¹' U
  have hY : IsOpen Y := hU.preimage (continuous_id.prodMk hR.continuous)
  refine ⟨v,Y,hv,hY,hBase,?_⟩
  intro z hz
  trace "near-ball-graph: restrict neighborhood"
  have hAt := hFamily (z,R z) hz
  trace "near-ball-graph: instantiated family"
  have hZ := hAt.1
  have hRadius := hAt.2.1
  have hNZ := hAt.2.2.1
  have hStrong := hAt.2.2.2.1
  have hCoverZ := hAt.2.2.2.2.1
  have hNear := hAt.2.2.2.2.2.1
  have hValue := hAt.2.2.2.2.2.2.2.1
  trace "near-ball-graph: family components"
  have hSmooth : ContDiffAt ℝ ∞
      (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 q R v) z := by
    unfold referencePhysicalNativeThreeHalfTraceSection
    exact contDiffAt_referenceMovingPhysicalNativeThreeHalfTrace g hg L y0 Φ B hData.1.1.1
        hcalc hF hO hD τ0 q R z v hR.contDiffAt
  trace "near-ball-graph: norm smoothness"
  have hPhysicalV : ∀ t ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) v.1)
        (referenceFramedPhysicalEndpoint g L Φ (q,((z,R z),t))) = 0 := by
    intro t ht
    have hClosed : t ∈ closedBall (0 : R3) 1 := ball_subset_closedBall ht
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
      (fun x => g (q • x)) v.1 u _ (hNear t hClosed)).trans
        (hphysical _ (hCoverZ ⟨t,hClosed,rfl⟩))
  trace "near-ball-graph: physical locality"
  refine ⟨hSmooth,hValue,?_⟩
  intro hzB hInv hNormal hWeak i
  exact referenceHighHorizontalAction_eq_movingAction_of_physical_harmonic
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel
      q hq R hR z hZ.le hRadius.le hzB hNZ i hInv hNormal hStrong hWeak v hPhysicalV

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighHorizontalAction_eq_movingAction_of_physical_harmonic
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceHighHorizontalTraceGraph_of_near_ball_harmonic
