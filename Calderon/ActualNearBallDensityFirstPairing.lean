import Calderon.ActualNearBallHorizontalTraceNeighborhood
import Calderon.ActualDensityFirstPairingDefect

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NEAR-BALL-DENSITY-FIRST-PAIRING-EXPANSION-v001.md. Derived actual graph eliminates the exact defect. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError MetricVolume SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referencePhysicalNativeThreeHalfTraceSection
  referenceHighMovingBoundaryActionFamily referenceHighMovingBoundaryAction referenceHighHorizontalAction
  referenceHighDensityFirstAction referenceMetricGramFrame sphereSobolevInclusionL sphereSobolevDualPairing
  referenceRadialEndpointInvertibleLocus

theorem exists_referenceDensityFirstPairing_neighborhood_of_near_ball_harmonic
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
      ∀ z ∈ Y,
        R z ≠ 0 ∧ (z,0) ∈ B ∧
        (∀ x : UnitSphere,
          (referenceFramedNormalizedJacobian g L Φ (q,((z,R z),x.val))).IsInvertible) ∧
        (q,(z,R z)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        ContDiffAt ℝ ∞ (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) z ∧
        (∀ x : UnitSphere,
          smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) v) x =
            u (referenceFramedPhysicalEndpoint g L Φ (q,((z,R z),x.val)))) ∧
        (∀ i : Fin 3, referenceHighHorizontalAction g L q (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) z i =
          referenceHighMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            R (q,z) i ((referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) z)) ∧
        ∀ (ψ : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ ψ → ∀ i : Fin 3,
          ContDiffAt ℝ ∞ (fun x => referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R ψ x i) z ∧
          fderiv ℝ (fun x : R3 => sphereSobolevDualPairing (-(1/2 : ℝ))
            (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (ψ x)))
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) x))) z
              (referenceMetricGramFrame g L (q,z) i) =
          sphereSobolevDualPairing (-(1/2 : ℝ)) (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R ψ z i))
            (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) ((referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v) z)) := by
  obtain ⟨v,Y0,hv,hY0,hyY0,hGraph⟩ :=
    exists_referenceHighHorizontalTraceGraph_neighborhood_of_near_ball_harmonic
      g hg L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel
      q hq R hR y hy hr hr0 hyB hInv hp S hS u hu hCover hphysical
  let Y := Y0 ∩ {z | R z ≠ 0}
  have hNZ : IsOpen {z | R z ≠ 0} := isOpen_ne_fun hR.continuous continuous_const
  refine ⟨v,Y,hv,hY0.inter hNZ,⟨hyY0,hr0⟩,?_⟩
  intro z hz
  have hAt := hGraph z hz.1
  have hB := hAt.1
  have hI := hAt.2.1
  have hP := hAt.2.2.1
  have hU := hAt.2.2.2.1
  have hValue := hAt.2.2.2.2.1
  have hAction := hAt.2.2.2.2.2
  refine ⟨hz.2,hB,hI,hP,hU,hValue,hAction,?_⟩
  intro ψ hψ i
  have hEta := contDiffAt_referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R ψ z i hψ.contDiffAt hR.contDiffAt hz.2 hI hP
  refine ⟨hEta,?_⟩
  let U : R3 → SphereSobolev (3/2 : ℝ) := referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q R v
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hFields :
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (z,R z)).IsInvertible ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(z,R z))).IsInvertible ∧
      (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(z,R z))).IsInvertible := by
    simpa only [referenceRadialEndpointInvertibleLocus,Set.mem_setOf_eq] using hP
  have hFamily := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A (U z))
    (referenceHighMovingBoundaryActionFamily_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,z) i hI)
  have hOriginal : referenceHighHorizontalAction g L q U z i =
      referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R z i hI (U z) :=
    (hAction i).trans hFamily
  have hProduct := fderiv_referenceHighDensityValuePairing_defect
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q R z i hI hFields.2.2 hFields.1 hFields.2.1
      ψ U (hψ.differentiable (by simp)).differentiableAt (hU.differentiableAt (by simp))
  let A : ℝ := sphereSobolevDualPairing (-(1/2 : ℝ)) (J (referenceHighDensityFirstAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R ψ z i)) (I (U z))
  have hZero : sphereSobolevDualPairing (1/2 : ℝ) (I (ψ z))
      (J (referenceHighHorizontalAction g L q U z i -
        referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R z i hI (U z))) = 0 := by
    have hDifference : referenceHighHorizontalAction g L q U z i -
        referenceHighMovingBoundaryAction g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          q R z i hI (U z) = 0 := sub_eq_zero.mpr hOriginal
    have hIncluded := (congrArg J hDifference).trans (map_zero J)
    have hScalar := congrArg
      (fun t : SphereSobolev (-(1/2 : ℝ)) => sphereSobolevDualPairing (1/2 : ℝ) (I (ψ z)) t) hIncluded
    exact hScalar.trans (by simp only [sphereSobolevDualPairing,inner_zero_right])
  exact hProduct.trans ((congrArg (fun b : ℝ => A+b) hZero).trans (add_zero A))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceDensityFirstPairing_neighborhood_of_near_ball_harmonic
