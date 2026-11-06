import Calderon.ActualLocalFiveHalfSourceGerm
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral SmoothMetricFrame MovingFrameConnection
  ActualNormalizedSecondMetricDrift
variable (g:MatrixField) (L:ℝ) (y0:R3)
  (Phi:ℝ→(R3×R3)→ℝ→R3×R3) (B:Set (R3×R3)) (eps C rho:ℝ)
  (H a:(ℝ×(R3×ℝ))×R3→Matrix (Fin 3) (Fin 3) ℝ)
  (w:(ℝ×(R3×ℝ))×R3→ℝ)
  (hData:JointConformalReferenceFramedDriftData g L y0 Phi B eps C rho H a w)
  (hg:IsAdmissibleMetric g) (hcalc:FixedSobolevCalculus)
  (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
  (tau0:UnitBallValueTrace)
attribute [local irreducible] referencePhysicalDensityOperator referencePhysicalDensityHalfFromFirstSections
  sphereSobolevInclusionL referenceFiveHalfDensityFirstActionInRoom referenceFiniteGaugeDensityFirstSection
  referenceJacobiBoundaryThreeHalfCoefficientFamily harmonicSphereSubspace

theorem exists_uniform_radius_local_original_physical_half_graph_germ
    (g2:MatrixField) (hg2:IsAdmissibleMetric g2) (hreg:FixedDirichletRegularity)
    (hKernel:UnitBallValueTraceKernel tau0):
    ∃ d0:ℝ,0 < d0 ∧ ∀ q∈Icc (0:ℝ) 1,
      ∀ (R:R3→ℝ),ContDiff ℝ ∞ R →
      ∀ (u:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ u →
      ∀ y:R3,‖y-y0‖ < rho → |R y| < d0 → R y≠0 →
      ∃ W:R3→SphereSobolev (1/2:ℝ),ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
        (fun z => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (W z))=ᶠ[𝓝 y]
        (fun z => referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg
          hcalc hF hO hD tau0 g2 q R
          (fun t => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u t)) z) := by
  obtain ⟨dX,hdX,hdXrho,G,E,d0,hd0,hd0X,HGraph⟩ :=
    exists_reference_commonRadius_same_physicalDensityHalfGraph
      g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 hg2 hreg hKernel
  refine ⟨d0,hd0,?_⟩
  intro q hq R hR u hu y hy hr hne
  let U:Set R3 := {z | ‖z-y0‖ < rho ∧ |R z| < d0 ∧ R z≠0}
  have hRne:IsOpen {z:R3 | R z≠0} :=
    (isClosed_singleton.preimage hR.continuous).isOpen_compl
  have hU:IsOpen U :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).inter
      ((isOpen_lt hR.continuous.abs continuous_const).inter hRne)
  obtain ⟨u0,hu0,hc0,hSupp,hSame⟩ :=
    exists_smooth_compact_fiveHalf_source_eq_germ_in_open_room U hU y ⟨hy,hr,hne⟩ u hu
  have hFull:=HGraph q hq R hR u0 hu0 hc0 (fun z hz => hSupp hz)
  extract_lets v etaInf W at hFull
  refine ⟨W,hFull.1,hFull.2.1,?_⟩
  have hLow:(fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u0 z))=ᶠ[𝓝 y]
      (fun z => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u z)) :=
    hSame.mono (fun z hz => congrArg (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) hz)
  have hGraph:=hFull.2.2.2.1
  filter_upwards [eventually_eventually_nhds.mpr hLow] with z hz
  exact (congrFun hGraph z).trans
    (referencePhysicalDensityOperator_congr_of_eventuallyEq g L y0 Phi B eps C rho H a w hData hg
      hcalc hF hO hD tau0 g2 q R _ _ z hz)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
