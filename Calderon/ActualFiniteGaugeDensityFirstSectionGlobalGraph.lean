import Calderon.ActualFiniteGaugeDensityFirstSectionGlobal
import Calderon.ActualFiniteGaugeDensityFirstSectionGraph
import Calderon.ActualPhysicalDensityOperatorLocality

/-! Global graph of the gauge density first section: the same eta, with the common choices
made before the cutoff. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteGaugeDensityFirstSection
  referenceFiniteHighHorizontalSection referenceFiniteGaugeAdjointMovingBoundaryFamily
  referenceStrongDriftFamily referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceFramedNormalizedJacobian sphereSobolevInclusionL sphereSobolevPartialSumL
  referenceHighDensityFirstAction referenceRadialEndpointInvertibleLocus

theorem exists_reference_commonRadius_finiteGaugeDensityFirstSection_globalGraph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∃ G : ReferenceGaugeNormalReciprocalRoom g L Φ a
          (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)),
        ∃ E : ReferenceJacobiCompactExtensionRoom
            (referenceJacobiBoundaryThreeHalfCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData)
            (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)),
          ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
            ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
            ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
            (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d ∧ R y ≠ 0) →
            ∀ i : Fin 3,
              ContDiff ℝ ∞ (fun y => referenceFiniteGaugeDensityFirstSection
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i) ∧
              HasCompactSupport (fun y => referenceFiniteGaugeDensityFirstSection
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i) ∧
              (fun y => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
                (referenceFiniteGaugeDensityFirstSection
                  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i)) =
              (fun y => referenceHighDensityFirstAction
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
                  (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) y i) := by
  classical
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  let Tube : Set (ℝ × (R3 × ℝ)) := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
  have hTube : IsCompact Tube := isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  let G := referenceGaugeNormalReciprocalRoomOfCompact
    g L Φ y0 B ε C ρ H a w hData hg Tube hTube
  have hE : Nonempty (ReferenceJacobiCompactExtensionRoom
      (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) Tube) :=
    exists_referenceJacobiCompactExtensionRoom g hg L y0 Φ B ε C ρ H a w hData Tube hTube
      (fun p hp => (hRoom p hp).2.2.2.2)
  let E := Classical.choice hE
  refine ⟨d,hd,hdρ,G,E,?_⟩
  intro n q hq R hR u hu hCompact hSupportRoom i
  let η : R3 → SphereSobolev (3/2 : ℝ) := fun y => referenceFiniteGaugeDensityFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i
  have hSupport : tsupport η ⊆ tsupport u :=
    tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u i
  have hSmooth : ContDiff ℝ ∞ η := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport u
    · have hAt := hSupportRoom y hy
      have hpTube : (q,(y,R y)) ∈ Tube := by
        refine ⟨hq,?_,abs_le.mp hAt.2.1.le⟩
        simpa only [mem_closedBall,dist_eq_norm] using hAt.1.le
      have hHighRoom : (referenceStrongDriftFamily
          g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible :=
        (hRoom (q,(y,R y)) hpTube).2.2.2.1.1
      exact contDiffAt_referenceFiniteGaugeDensityFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i
          hu.contDiffAt hR.contDiffAt hAt.2.2 hHighRoom
    · have hyη : y ∉ tsupport η := fun h => hy (hSupport h)
      have hZero : η =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp hyη
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) y).congr_of_eventuallyEq hZero
  refine ⟨hSmooth,hCompact.of_isClosed_subset (isClosed_tsupport η) hSupport,?_⟩
  let v : R3 → SphereSobolev (3/2 : ℝ) := fun y => sphereSobolevPartialSumL (3/2 : ℝ) n (u y)
  let T : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
  let X : R3 → SphereSobolev (1/2 : ℝ) := fun y => referenceHighDensityFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v y i
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hT : Continuous T := continuous_const.prodMk (continuous_id.prodMk hR.continuous)
  have hVSupport : tsupport v ⊆ tsupport u :=
    tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (3/2 : ℝ) n)) u
  have hXSupport : tsupport X ⊆ tsupport u :=
    (tsupport_referenceHighDensityFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R v i).trans hVSupport
  funext y
  change I (η y) = X y
  by_cases hy : y ∈ tsupport u
  · have hAt := hSupportRoom y hy
    have hpTube : T y ∈ Tube := by
      refine ⟨hq,?_,abs_le.mp hAt.2.1.le⟩
      simpa only [mem_closedBall,dist_eq_norm] using hAt.1.le
    have hNearBase : ∀ᶠ z in 𝓝 y, ‖z-y0‖ < ρ :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hAt.1
    have hNearRadius : ∀ᶠ z in 𝓝 y, |R z| < d :=
      (isOpen_lt hR.continuous.abs continuous_const).mem_nhds hAt.2.1
    have hNearG : ∀ᶠ z in 𝓝 y, T z ∈ G.parameterRoom :=
      hT.continuousAt.eventually (G.roomOpen.mem_nhds (G.containsCompact hpTube))
    have hNear : ∀ᶠ z in 𝓝 y, ‖z-y0‖ ≤ ρ ∧
        TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a ((q,(z,R z)),x)) lam Lam ∧
        (∀ x ∈ (ballOpens : Set R3),
          ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(z,R z)),x)‖ ≤ lam/4) ∧
        (q,(z,R z)) ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        (q,(z,R z)) ∈ G.parameterRoom := by
      filter_upwards [hNearBase,hNearRadius,hNearG] with z hzBase hzRadius hzG
      have hzTube : T z ∈ Tube := by
        refine ⟨hq,?_,abs_le.mp hzRadius.le⟩
        simpa only [mem_closedBall,dist_eq_norm] using hzBase.le
      have hzPoint := hRoom (T z) hzTube
      exact ⟨hzBase.le,hzPoint.1,hzPoint.2.1.1,hzPoint.2.2.1,hzG⟩
    exact (eventually_sphereSobolevInclusionL_referenceFiniteGaugeDensityFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E hreg hKernel
        n q hq R hR u hu y hpTube lam Lam hNear i).self_of_nhds
  · have hEtaZero : η y = 0 := image_eq_zero_of_notMem_tsupport
      (f := η) (x := y) (fun h => hy (hSupport h))
    have hXZero : X y = 0 := image_eq_zero_of_notMem_tsupport
      (f := X) (x := y) (fun h => hy (hXSupport h))
    exact (congrArg I hEtaZero).trans ((map_zero I).trans hXZero.symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteGaugeDensityFirstSection_globalGraph
