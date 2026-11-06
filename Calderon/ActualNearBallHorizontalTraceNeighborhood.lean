import Calderon.ActualNearBallHorizontalTraceGraph
import Calderon.ActualHighMovingBoundaryFamily

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-TRACE-GRAPH-NEIGHBORHOOD-EXPANSION-v001.md. Derived original inverse/graph neighborhood. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic ConnectionError MetricVolume

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceFramedNormalizedJacobian referenceFramedPhysicalEndpoint
  referencePhysicalNativeThreeHalfTraceSection referenceHighHorizontalAction
  referenceHighMovingBoundaryActionFamily referenceHighMovingBoundaryAction
  referencePhysicalPullbackData referenceRadialEndpointInvertibleLocus

include hg hData in
theorem eventually_referenceFramedNormalizedJacobian_moving_sphere_isInvertible
    (q : ℝ) (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) (y : R3)
    (hInv : ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),x.val))).IsInvertible) :
    ∀ᶠ z in 𝓝 y, ∀ x : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((z,R z),x.val))).IsInvertible := by
  let J : R3 × R3 → R3 →L[ℝ] R3 := fun p =>
    referenceFramedNormalizedJacobian g L Φ (q,((p.1,R p.1),p.2))
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk (hR.comp contDiff_fst)).prodMk contDiff_snd))
  have hOpen : IsOpen {p : R3 × R3 | (J p).IsInvertible} := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    exact hJ.continuous.continuousAt.eventually hp.eventually_nhds
  have hNear : ∀ᶠ z in 𝓝 y, ∀ t ∈ sphere (0 : R3) 1, (J (z,t)).IsInvertible := by
    apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
    intro t ht
    exact hOpen.mem_nhds (hInv ⟨t,ht⟩)
  filter_upwards [hNear] with z hz
  intro x
  exact hz x.val x.property

theorem exists_referenceHighHorizontalTraceGraph_neighborhood_of_near_ball_harmonic
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
        (z,0) ∈ B ∧
        (∀ x : UnitSphere,
          (referenceFramedNormalizedJacobian g L Φ (q,((z,R z),x.val))).IsInvertible) ∧
        (q,(z,R z)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        ContDiffAt ℝ ∞
          (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
            hcalc hF hO hD τ0 q R v) z ∧
        (∀ x : UnitSphere,
          smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q z (R z) v) x =
            u (referenceFramedPhysicalEndpoint g L Φ (q,((z,R z),x.val)))) ∧
        ∀ i : Fin 3,
          referenceHighHorizontalAction g L q
            (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
              hcalc hF hO hD τ0 q R v) z i =
          referenceHighMovingBoundaryActionFamily g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
            R (q,z) i
            (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
              hcalc hF hO hD τ0 q R v z) := by
  have hpFields : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (y,R y)).IsInvertible ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,R y))).IsInvertible ∧
      (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,R y))).IsInvertible := by
    simpa only [referenceRadialEndpointInvertibleLocus,Set.mem_setOf_eq] using hp
  obtain ⟨v,Y0,hv,hY0,hyY0,hGraph⟩ := exists_referenceHighHorizontalTraceGraph_of_near_ball_harmonic
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 hKernel
      q hq R hR y hy hr hr0 hpFields.1 S hS u hu hCover hphysical
  have hNearInv := eventually_referenceFramedNormalizedJacobian_moving_sphere_isInvertible
    g hg L y0 Φ B ε C ρ H a w hData q R hR y hInv
  have hCenter : Continuous (fun z : R3 => (z,(0 : R3))) :=
    continuous_id.prodMk continuous_const
  have hNearB : ∀ᶠ z in 𝓝 y, (z,0) ∈ B :=
    hCenter.continuousAt.eventually (hData.1.1.1.1.mem_nhds hyB)
  have hParameter : Continuous (fun z : R3 => (q,(z,R z))) :=
    continuous_const.prodMk (continuous_id.prodMk hR.continuous)
  have hNearP : ∀ᶠ z in 𝓝 y,
      (q,(z,R z)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
    hParameter.continuousAt.eventually
      ((isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)
  have hNear : ∀ᶠ z in 𝓝 y, z ∈ Y0 ∧ (z,0) ∈ B ∧
      (∀ x : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((z,R z),x.val))).IsInvertible) ∧
      (q,(z,R z)) ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := by
    filter_upwards [hY0.mem_nhds hyY0,hNearB,hNearInv,hNearP] with z hz hB hI hP
    exact ⟨hz,hB,hI,hP⟩
  obtain ⟨Y,hYsub,hYopen,hyY⟩ := _root_.mem_nhds_iff.mp hNear
  refine ⟨v,Y,hv,hYopen,hyY,?_⟩
  intro z hz
  obtain ⟨hzY0,hB,hI,hP⟩ := hYsub hz
  obtain ⟨hSmooth,hValue,hAction⟩ := hGraph z hzY0
  have hPFields : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q (z,R z)).IsInvertible ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(z,R z))).IsInvertible ∧
      (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(z,R z))).IsInvertible := by
    simpa only [referenceRadialEndpointInvertibleLocus,Set.mem_setOf_eq] using hP
  refine ⟨hB,hI,hP,hSmooth,hValue,?_⟩
  intro i
  have hOriginal := hAction hB hI hPFields.2.2 hPFields.2.1 i
  have hFamily := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A
      (referencePhysicalNativeThreeHalfTraceSection g hg L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 q R v z))
    (referenceHighMovingBoundaryActionFamily_eq
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,z) i hI)
  exact hOriginal.trans hFamily.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_referenceFramedNormalizedJacobian_moving_sphere_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceHighHorizontalTraceGraph_neighborhood_of_near_ball_harmonic
