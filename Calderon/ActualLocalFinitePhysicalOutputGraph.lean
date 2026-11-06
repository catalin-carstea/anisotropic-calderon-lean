import Calderon.ActualCommonRadiusWeightedSphereGraph
import Calderon.ActualPhysicalDensityOperatorLocality
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame ActualFiniteHarmonicCore
  ReferenceDensityBounds ConformalDepth WeightedBaseSpectral MovingFrameConnection ActualNormalizedSecondMetricDrift
variable (g:MatrixField) (L:ℝ) (y0:R3)
  (Phi:ℝ→(R3×R3)→ℝ→R3×R3) (B:Set (R3×R3)) (eps C rho:ℝ)
  (H a:(ℝ×(R3×ℝ))×R3→Matrix (Fin 3) (Fin 3) ℝ)
  (w:(ℝ×(R3×ℝ))×R3→ℝ)
  (hData:JointConformalReferenceFramedDriftData g L y0 Phi B eps C rho H a w)
  (hg:IsAdmissibleMetric g) (hcalc:FixedSobolevCalculus)
  (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace)
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL harmonicSphereSubspace
  referencePhysicalDensityHalfFromFirstSections referenceFiveHalfDensityFirstActionInRoom
  referenceFiniteGaugePhysicalDensityHalfSection referenceJacobiBoundaryThreeHalfCoefficientFamily

private lemma physical_output_support_of_original_negative_graph
    (g2:MatrixField) (q:ℝ) (R:R3→ℝ) (u:R3→SphereSobolev (3/2:ℝ)) (F:R3→SphereL2)
    (K:Set R3) (hK:IsClosed K) (hUSupp:tsupport u⊆K)
    (hGraph:∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F y))=
      referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R u y):
    tsupport F⊆K := by
  apply closure_minimal ?_ hK
  intro y hy
  by_contra hk
  apply hy
  apply (sphereSobolevZeroEquiv hO hD).injective
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have hSupp:tsupport (fun z => referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg
      hcalc hF hO hD tau0 g2 q R u z)⊆K :=
    (tsupport_referencePhysicalDensityOperator_subset g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R u).trans hUSupp
  have hZero:referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R u y=0 :=
    image_eq_zero_of_notMem_tsupport (fun hz => hk (hSupp hz))
  rw [hGraph y,hZero,map_zero,map_zero]

theorem exists_common_radius_actual_physical_finite_output_graph
    (g2:MatrixField) (hg2:IsAdmissibleMetric g2) (hreg:FixedDirichletRegularity)
    (hKernel:UnitBallValueTraceKernel tau0):
    ∃ d0:ℝ,0 < d0 ∧ ∀ q∈Icc (0:ℝ) 1,
      ∀ (R:R3→ℝ),ContDiff ℝ ∞ R →
      ∀ (u:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y∈tsupport u,‖y-y0‖ < rho ∧ |R y| < d0 ∧ R y≠0) →
      let v:R3→SphereSobolev (3/2:ℝ) := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
      ∃ (F:ℕ→R3→SphereL2) (f:R3→SphereL2),
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport u ∧
        ∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
          referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R
            (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) y) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport u ∧
      (∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
        referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R v y) ∧
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*‖F n y-f y‖^2) atTop (𝓝 0) := by
  obtain ⟨dX,hdX,hdXrho,G,E,d0,hd0,hd0X,HGraph⟩ :=
    exists_reference_commonRadius_same_physicalDensityWeightedSphereGraph
      g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 hg2 hreg hKernel
  refine ⟨d0,hd0,?_⟩
  intro q hq R hR u hu hc hRoom
  dsimp only
  have hFull:=HGraph q hq R hR u hu hc hRoom
  extract_lets v etaInf Wlim F f at hFull
  have hLowSupp:tsupport v⊆tsupport u :=
    tsupport_comp_subset (map_zero (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) u
  refine ⟨F,f,?_,hFull.2.1,hFull.2.2.1,?_,?_,hFull.2.2.2.2.2⟩
  · intro n
    have hn:=hFull.1 n
    have hGN:∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
        referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R
          (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) y := fun y => congrFun hn.2.2.2 y
    refine ⟨hn.1,hn.2.1,?_,hGN⟩
    apply physical_output_support_of_original_negative_graph g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0
      g2 q R _ (F n) (tsupport u) (isClosed_tsupport u) _ hGN
    exact (tsupport_comp_subset (map_zero (sphereSobolevPartialSumL (3/2:ℝ) n)) v).trans hLowSupp
  · exact physical_output_support_of_original_negative_graph g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0
      g2 q R v f (tsupport u) (isClosed_tsupport u) hLowSupp (fun y => congrFun hFull.2.2.2.2.1 y)
  · exact fun y => congrFun hFull.2.2.2.2.1 y

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
