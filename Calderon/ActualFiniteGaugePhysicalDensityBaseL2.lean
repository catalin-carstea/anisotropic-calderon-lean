import Calderon.ActualFiniteGaugePhysicalDensityHalfSectionGraph
import Calderon.ActualFiniteGaugePhysicalDensityHalfSectionSmoothness
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-FINITE-GAUGE-PHYSICAL-BASE-L2-UPFRONT-v001.md. ONE actual W, no pointwise output choice. -/
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

attribute [local irreducible] referenceFiniteGaugePhysicalDensityHalfSection
  referenceFiniteGaugeDensityFirstSection referencePhysicalDensityOperator sphereSobolevInclusionL
  sphereSobolevPartialSumL sphereSobolevZeroEquiv referenceRadialEndpointInvertibleLocus
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily referenceFramedNormalizedJacobian

theorem exists_reference_commonRadius_finitePhysicalDensityOperator_baseL2_of_gauge
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
        ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
        ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
        (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < δ ∧ R y ≠ 0) →
        ∃ f : R3 → SphereL2, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
          MemLp f 2 (volume : Measure R3) ∧
          ∀ y : R3,
            sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y)) =
              referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
                (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) y := by
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
  refine ⟨d/2,by positivity,(by linarith),?_⟩
  intro n q hq R hR u hu hCompact hSupportRoom
  let W : R3 → SphereSobolev (1/2 : ℝ) := fun y => referenceFiniteGaugePhysicalDensityHalfSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R u y
  let v : R3 → SphereSobolev (3/2 : ℝ) := fun y => sphereSobolevPartialSumL (3/2 : ℝ) n (u y)
  let T : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
  have hT : Continuous T := continuous_const.prodMk (continuous_id.prodMk hR.continuous)
  have hPointTube (y : R3) (hy : y ∈ tsupport u) : T y ∈ Tube := by
    have hAt := hSupportRoom y hy
    refine ⟨hq,?_,abs_le.mp (show |R y| ≤ d by linarith [hAt.2.1])⟩
    simpa only [mem_closedBall,dist_eq_norm] using hAt.1.le
  have hWSupport : tsupport W ⊆ tsupport u :=
    tsupport_referenceFiniteGaugePhysicalDensityHalfSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 n q R u
  have hWSmooth : ContDiff ℝ ∞ W := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport u
    · have hAt := hSupportRoom y hy
      have hPoint := hRoom (T y) (hPointTube y hy)
      exact contDiffAt_referenceFiniteGaugePhysicalDensityHalfSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 hg2 hreg n q R u y
          hu.contDiffAt hR.contDiffAt hAt.2.2 hPoint.2.2.2.1.1 hPoint.2.2.2.2 hPoint.2.2.1
    · have hyW : y ∉ tsupport W := fun h => hy (hWSupport h)
      have hZero : W =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp hyW
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) y).congr_of_eventuallyEq hZero
  have hWCompact : HasCompactSupport W :=
    hCompact.of_isClosed_subset (isClosed_tsupport W) hWSupport
  have hOnGraph (y : R3) (hy : y ∈ tsupport u) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (W y) =
        referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y := by
    have hAt := hSupportRoom y hy
    have hpTube := hPointTube y hy
    have hPoint := hRoom (T y) hpTube
    have hNearBase : ∀ᶠ z in 𝓝 y, ‖z-y0‖ < ρ :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hAt.1
    have hNearRadius : ∀ᶠ z in 𝓝 y, |R z| < d :=
      (isOpen_lt (hR.continuous.abs) continuous_const).mem_nhds (show |R y| < d by linarith [hAt.2.1])
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
    have hWeak : (referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (T y)).IsInvertible :=
      isInvertible_referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (T y) lam hPoint.2.1
    exact sphereSobolevInclusionL_referenceFiniteGaugePhysicalDensityHalfSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E g2 hreg hKernel n q hq R hR u hu y hpTube lam Lam hNear
        hAt.2.2 hPoint.2.2.2.1.1 hPoint.2.2.2.2 hWeak
  have hVSupport : tsupport v ⊆ tsupport u :=
    tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (3/2 : ℝ) n)) u
  have hPSupport : tsupport (fun y => referencePhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y) ⊆ tsupport u :=
    (tsupport_referencePhysicalDensityOperator_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v).trans hVSupport
  have hWGraph (y : R3) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (W y) =
        referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y := by
    by_cases hy : y ∈ tsupport u
    · exact hOnGraph y hy
    · have hWZero : W y = 0 := image_eq_zero_of_notMem_tsupport
        (f := W) (x := y) (fun h => hy (hWSupport h))
      have hPZero : referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v y = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun z => referencePhysicalDensityOperator g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R v z)
          (x := y) (fun h => hy (hPSupport h))
      let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      exact (congrArg J hWZero).trans ((map_zero J).trans hPZero.symm)
  let Z := sphereSobolevZeroEquiv hO hD
  let I0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let T0 : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereL2 :=
    Z.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp I0
  let f : R3 → SphereL2 := fun y => Z.symm (I0 (W y))
  have hfSmooth : ContDiff ℝ ∞ f := T0.contDiff.comp hWSmooth
  have hfSupport : tsupport f ⊆ tsupport W := tsupport_comp_subset (map_zero T0) W
  have hfCompact : HasCompactSupport f :=
    hWCompact.of_isClosed_subset (isClosed_tsupport f) hfSupport
  have hfMem : MemLp f 2 (volume : Measure R3) :=
    hfSmooth.continuous.memLp_of_hasCompactSupport hfCompact
  refine ⟨f,hfSmooth,hfCompact,hfMem,?_⟩
  intro y
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num))
    (Z.apply_symm_apply (I0 (W y)))
  have hTrans := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (W y))
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  exact hCancel.trans (hTrans.trans (hWGraph y))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finitePhysicalDensityOperator_baseL2_of_gauge
