import Calderon.ActualJacobiNativeCenterTrace
import Calderon.ActualMovingPhysicalRadius

/-! The SAME actual center trace plus the genuine logarithmic-radius term.
Only the native coarse bulk-H2 to sphere-L2 topology is asserted. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame

def referenceRadiusHorizontalLogDerivative (g : MatrixField) (L q : ℝ)
    (R : R3 → ℝ) (y : R3) (i : Fin 3) : ℝ :=
  fderiv ℝ (fun x => Real.log (R x)) y
    (conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i))

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceNativeMovingRadiusTraceOperator
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ)
    (R : R3 → ℝ) (y : R3) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) :
    BallSobolev 2 →L[ℝ] SphereL2 :=
  referenceNativeCenterTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q y (R y) i hInv +
  referenceRadiusHorizontalLogDerivative g L q R y i •
    referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,R y)

def referencePhysicalMovingHorizontalSphere (q : ℝ) (R : R3 → ℝ) (y : R3)
    (i : Fin 3) (v : SmoothData) : C(UnitSphere, ℝ) :=
  referencePhysicalCenterHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q y (R y) i v +
  referenceRadiusHorizontalLogDerivative g L q R y i •
    smoothRadialSphere (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v)

theorem referencePhysicalMovingHorizontalSphere_source_derivative
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : (y,0) ∈ B) (hr : R y ≠ 0) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (v : SmoothData) (x : UnitSphere) :
    let F : R3 → R3 →L[ℝ] R3 := fun z => conformalReferenceGramFrameOperatorJoint g L (q,z)
    let Γ := coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q))
    fderiv ℝ (fun p : R3 × R3 => v.1
      (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,R p.1),p.2)))) (y,x.val)
      (F y (coordinateVector i),framedParallelAngularVelocity F Γ y (F y (coordinateVector i)) x.val) =
      referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R y i v x := by
  dsimp only
  rw [fderiv_referencePhysicalSphereValue_moving_radius_horizontal
    g hg L y0 Φ B hData.1.1.1 q hq y x.val hy R hR hr i v (hInv x)]
  have hCenter := fderiv_referencePhysicalSphereValue_center_horizontal_decomposition
    g hg L y0 Φ B hData.1.1.1 q hq y x.val hy (R y) hr i v (hInv x)
  dsimp only at hCenter
  rw [fderiv_referencePhysicalSphereValue_center_horizontal
    g hg L y0 Φ B hData.1.1.1 q y x.val (R y) i v] at hCenter
  change _ =
    fderiv ℝ v.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,R y),x.val)))
      (referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,R y),x.val))) +
    referenceRadiusHorizontalLogDerivative g L q R y i *
      fderiv ℝ (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v).1 x.val x.val
  rw [hCenter]
  rfl

theorem referenceNativeMovingRadiusTraceOperator_physical_smooth
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ)
    (y : R3) (hy : (y,0) ∈ B) (hr : R y ≠ 0) (i : Fin 3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (v : SmoothData)
    (hLift : referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)
      (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v)) =
      smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v)) :
    referenceNativeMovingRadiusTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q R y i hInv
      (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v)) =
        (ContinuousMap.toLp 2 sphereProbability ℝ)
          (referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R y i v) := by
  have hCenter := referenceNativeCenterTraceOperator_physical_smooth
    g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q hq y hy (R y) hr i hInv v hLift
  have hRadial : referenceNativeRadialTraceOperatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q (y,R y)
      (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v)) =
      (ContinuousMap.toLp 2 sphereProbability ℝ)
        (smoothRadialSphere (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y (R y) v)) := by
    rw [referenceNativeRadialTraceOperatorFamily,ContinuousLinearMap.comp_apply,hLift,
      outwardRadialTraceL_smoothBallSobolev]
  rw [referenceNativeMovingRadiusTraceOperator,add_apply,smul_apply,hCenter,hRadial,
    ← map_smul,← map_add]
  rfl

theorem exists_referenceNativeMovingRadiusTrace_of_near_ball_harmonic
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ < 4*ρ) (hr : |R y| < 4*ρ) (hr0 : R y ≠ 0)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (hCover : (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,R y),z))) ''
      closedBall (0 : R3) 1 ⊆ S)
    (hphysical : ∀ x ∈ S,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u) x = 0) :
    ∃ (v : SmoothData) (Y : Set R3), HasCompactSupport v.1 ∧ IsOpen Y ∧ y ∈ Y ∧
      ∀ z ∈ Y, ∀ hzB : (z,0) ∈ B,
        ∀ hInv : ∀ x : UnitSphere,
          (referenceFramedNormalizedJacobian g L Φ (q,((z,R z),x.val))).IsInvertible,
        ∀ i : Fin 3,
          referenceNativeMovingRadiusTraceOperator g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q R z i hInv
            (smoothBallSobolev 2 (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) v)) =
              (ContinuousMap.toLp 2 sphereProbability ℝ)
                (referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R z i v) ∧
          ∀ x : UnitSphere,
            let F : R3 → R3 →L[ℝ] R3 := fun t => conformalReferenceGramFrameOperatorJoint g L (q,t)
            let Γ := coordinateConnectionField
              (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
              (metricOperatorField (conformalReferenceMatrix g L q))
            referencePhysicalMovingHorizontalSphere g hg L y0 Φ B ε C ρ H a w hData q R z i v x =
              fderiv ℝ (fun p : R3 × R3 => u
                (referenceFramedPhysicalEndpoint g L Φ (q,((p.1,R p.1),p.2)))) (z,x.val)
                (F z (coordinateVector i),framedParallelAngularVelocity F Γ z (F z (coordinateVector i)) x.val) := by
  obtain ⟨v,U,hv,hU,hBase,hFamily⟩ := exists_referenceHarmonicLift_family_of_near_ball_harmonic
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg 0 q hq y hy (R y) hr hr0 hi S hS u hu hCover hphysical
  let Y : Set R3 := (fun z : R3 => (z,R z)) ⁻¹' U
  have hY : IsOpen Y := hU.preimage (continuous_id.prodMk hR.continuous)
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let X : R3 × R3 → R3 := fun p =>
    referenceFramedPhysicalEndpoint g L Φ (q,((p.1,R p.1),p.2))
  have hX : Continuous X :=
    ((contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk (hR.comp contDiff_fst)).prodMk contDiff_snd))).continuous
  refine ⟨v,Y,hv,hY,hBase,?_⟩
  intro z hz hzB hInv i
  obtain ⟨hZ,hRadius,hNZ,hI,hCoverZ,hNear,hLift,hValue,hRad⟩ := hFamily (z,R z) hz
  refine ⟨referenceNativeMovingRadiusTraceOperator_physical_smooth
    g hg L y0 Φ B ε C ρ H a w hData hcalc τ0 q hq R z hzB hNZ i hInv v hLift,?_⟩
  intro x
  dsimp only
  have hn : ‖x.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using x.property
  have hx : x.val ∈ closedBall (0 : R3) 1 := by
    simpa only [mem_closedBall,dist_zero_right,hn] using (le_refl (1 : ℝ))
  have hGerm : (fun p : R3 × R3 => v.1 (X p)) =ᶠ[𝓝 (z,x.val)]
      (fun p : R3 × R3 => u (X p)) :=
    (hNear x.val hx).comp_tendsto hX.continuousAt
  have hDerivative := hGerm.fderiv_eq (𝕜 := ℝ)
  have hSource := referencePhysicalMovingHorizontalSphere_source_derivative
    g hg L y0 Φ B ε C ρ H a w hData q hq R hR z hzB hNZ i hInv v x
  dsimp only at hSource
  exact hSource.symm.trans (congrArg (fun A : (R3 × R3) →L[ℝ] ℝ => A
    (conformalReferenceGramFrameOperatorJoint g L (q,z) (coordinateVector i),
      framedParallelAngularVelocity (fun t => conformalReferenceGramFrameOperatorJoint g L (q,t))
        (coordinateConnectionField
          (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
          (metricOperatorField (conformalReferenceMatrix g L q))) z
        (conformalReferenceGramFrameOperatorJoint g L (q,z) (coordinateVector i)) x.val)) hDerivative)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
