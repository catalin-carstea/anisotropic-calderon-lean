import Calderon.ActualPhysicalDensityPairingContraction
import Calderon.ActualNearBallDensityFirstPairing
import Calderon.ActualPhysicalDensityOperator
import Calderon.ActualNormalizedScalarFrameOperator

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NEAR-BALL-PHYSICAL-DENSITY-PAIRING-EXPANSION-v001.md. Literal physical P pairing on the derived actual core. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError MetricVolume SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift NativeH2ThreeHalfValueTrace

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


attribute [local irreducible] nativeThreeHalfValueTraceL smoothBallSobolev referencePhysicalPullbackData

theorem contDiff_referencePhysicalNativeThreeHalfTraceSection
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (v : SmoothData) :
    ContDiff ℝ ∞ (referencePhysicalNativeThreeHalfTraceSection
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  unfold referencePhysicalNativeThreeHalfTraceSection
  exact contDiffAt_referenceMovingPhysicalNativeThreeHalfTrace
    g hg L y0 Φ B hData.1.1.1 hcalc hF hO hD τ0 q R z v hR.contDiffAt

attribute [local irreducible] referencePhysicalNativeThreeHalfTraceSection
  referenceHighMovingBoundaryActionFamily referenceHighMovingBoundaryAction referenceHighHorizontalAction
  referenceHighDensityFirstAction referenceLowerDensityFirstAction referenceDensityCovariantSecondAction
  referenceMetricGramFrame referenceFrameConnectionCoefficient sphereSobolevInclusionL sphereSobolevDualPairing
  referenceRadialEndpointInvertibleLocus referenceDensityPrincipalFrameCoefficient normalizedSecondDriftFrameJoint
  referencePhysicalDensityOperator normalizedSecondLaplacian
  referenceFramedNormalizedJacobian referenceFramedPhysicalEndpoint
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily

theorem exists_referencePhysicalDensityPairing_neighborhood_of_near_ball_harmonic
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ < 4*ρ) (hr : |R y| < 4*ρ) (hr0 : R y ≠ 0)
    (hyB : (y,0) ∈ B)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible)
    (hp : (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (hCover : (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,R y),z))) ''
      closedBall (0 : R3) 1 ⊆ S)
    (hphysical : ∀ x ∈ S,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u) x = 0) :
    ∃ (v : SmoothData) (Y : Set R3), HasCompactSupport v.1 ∧ IsOpen Y ∧ y ∈ Y ∧
      (∀ z ∈ Y, ∀ x : UnitSphere,
        smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) v) x =
          u (referenceFramedPhysicalEndpoint g L Φ (q,((z,R z),x.val)))) ∧
      ∀ (ψ : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ ψ → ∀ z ∈ Y,
        R z * normalizedSecondLaplacian g g2 L q (fun x : R3 => sphereSobolevDualPairing (-(1/2 : ℝ)) (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (ψ x))) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) x))) z =
        sphereSobolevDualPairing (-(1/2 : ℝ)) (referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R ψ z) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) z)) := by
  obtain ⟨v,Y,hv,hY,hyY,hFirst⟩ :=
    exists_referenceDensityFirstPairing_neighborhood_of_near_ball_harmonic
      g hg L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel
      q hq R hR y hy hr hr0 hyB hInv hp S hS u hu hCover hphysical
  refine ⟨v,Y,hv,hY,hyY,?_,?_⟩
  · intro z hz
    exact (hFirst z hz).2.2.2.2.2.1
  intro ψ hψ
  let U : R3 → SphereSobolev (3/2 : ℝ) := referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let f : R3 → ℝ := fun x => sphereSobolevDualPairing (-(1/2 : ℝ)) (J (I (ψ x))) (I (U x))
  let η : Fin 3 → R3 → SphereSobolev (1/2 : ℝ) := fun j x => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R ψ x j
  have hUglobal : ContDiff ℝ ∞ U :=
    contDiff_referencePhysicalNativeThreeHalfTraceSection
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R hR v
  have hf : ContDiff ℝ ∞ f := by
    dsimp only [f]
    simp only [sphereSobolevDualPairing]
    exact (J.contDiff.comp (I.contDiff.comp hψ)).inner ℝ (I.contDiff.comp hUglobal)
  intro z hz
  have hAt := hFirst z hz
  have hRadius := hAt.1
  have hB := hAt.2.1
  have hI := hAt.2.2.1
  have hP := hAt.2.2.2.1
  have hU := hAt.2.2.2.2.1
  have hValue := hAt.2.2.2.2.2.1
  have hGraph := hAt.2.2.2.2.2.2.1
  have hPair := hAt.2.2.2.2.2.2.2
  let e : Fin 3 → R3 := fun i => referenceMetricGramFrame g L (q,z) i
  have hFields :
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (z,R z)).IsInvertible ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(z,R z))).IsInvertible ∧
      (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(z,R z))).IsInvertible := by
    simpa only [referenceRadialEndpointInvertibleLocus,Set.mem_setOf_eq] using hP
  have hFirstScalar (i : Fin 3) : fderiv ℝ f z (e i) =
      sphereSobolevDualPairing (-(1/2 : ℝ)) (J (η i z)) (I (U z)) :=
    (hPair ψ hψ i).2
  trace "actual P pairing: first derivative graph"
  have hSecondScalar (i j : Fin 3) :
      fderiv ℝ (fun x => fderiv ℝ f x (referenceMetricGramFrame g L (q,x) j)) z (e i) =
      sphereSobolevDualPairing (-(1/2 : ℝ))
        (referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) z i) (I (U z)) := by
    have hNear : (fun x => fderiv ℝ f x (referenceMetricGramFrame g L (q,x) j)) =ᶠ[𝓝 z]
        (fun x => sphereSobolevDualPairing (-(1/2 : ℝ)) (J (η j x)) (I (U x))) := by
      filter_upwards [hY.mem_nhds hz] with x hx
      exact ((hFirst x hx).2.2.2.2.2.2.2 ψ hψ j).2
    have hDerivative := congrArg (fun A : R3 →L[ℝ] ℝ => A (e i)) hNear.fderiv_eq
    have hEta : DifferentiableAt ℝ (η j) z :=
      ((hPair ψ hψ j).1).differentiableAt (by simp)
    have hProduct := fderiv_referenceLowerDensityValuePairing_defect
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R z i hI hFields.2.2 hFields.1 hFields.2.1 (η j) U
        hEta (hU.differentiableAt (by simp))
    have hFamily := congrArg
      (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A (U z))
      (referenceHighMovingBoundaryActionFamily_eq g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,z) i hI)
    have hOriginal : referenceHighHorizontalAction g L q U z i =
        referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R z i hI (U z) := (hGraph i).trans hFamily
    let A : ℝ := sphereSobolevDualPairing (-(1/2 : ℝ))
      (referenceLowerDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R (η j) z i) (I (U z))
    have hZero : sphereSobolevDualPairing (1/2 : ℝ) (η j z)
        (J (referenceHighHorizontalAction g L q U z i -
          referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R z i hI (U z))) = 0 := by
      rw [hOriginal,sub_self,map_zero]
      simp only [sphereSobolevDualPairing,inner_zero_right]
    exact hDerivative.trans (hProduct.trans
      ((congrArg (fun b : ℝ => A+b) hZero).trans (add_zero A)))
  trace "actual P pairing: second derivative graph"
  exact referencePhysicalDensityOperator_pairing_of_frame_derivative_graphs
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 hg2 q R ψ f z (U z)
      hf hFirstScalar hSecondScalar

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referencePhysicalNativeThreeHalfTraceSection
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePhysicalDensityPairing_neighborhood_of_near_ball_harmonic
