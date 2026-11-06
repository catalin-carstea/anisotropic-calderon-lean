import Calderon.ActualLocalFinitePhysicalOutputGraph
import Calderon.ActualPacketPhysicalOperatorCoherence
import Calderon.ActualRadiusBootstrapSmallJets
import Calderon.ActualCenteredNativeCover
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore ReferenceDensityBounds WeightedBaseSpectral
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace

theorem exists_native_cover_uniform_actual_local_finite_physical_graphs
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      (∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling) ∧
      ∀ i:Fin cover.count,∀ (u:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u⊆cylinder∩(cover.packet i).centers →
      let v:R3→SphereSobolev (3/2:ℝ) := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
      ∃ (F:ℕ→R3→SphereL2) (f:R3→SphereL2),
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport u ∧
        ∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (v z)) i y) ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport u ∧
      (∀ y:R3,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p v i y) ∧
      Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F n y-f y‖^2) atTop (𝓝 0) := by
  have hEach (i:Fin cover.count) := exists_common_radius_actual_physical_finite_output_graph
    S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo
    (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w
    (cover.packet i).native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 S.g2_admissible hreg hKernel
  choose di hdi HD using hEach
  obtain ⟨d,hd,hdAll⟩ := Geometry.exists_pos_le_finite di hdi
  let b:ℝ := min d cover.radiusCeiling
  have hb:0 < b := lt_min hd cover.radius_positive
  obtain ⟨pG,hpG,eps0,heps0,heps01,HG⟩ := exists_uniform_referenceRadius_small_ordinary_jets_of_bootstrap
    S.g1 S.g1_admissible cylinder Geometry.isCompact_cylinder L hL (b/2) (half_pos hb)
  refine ⟨max pG 2,le_max_right _ _,eps0,heps0,heps01,?_⟩
  intro p hp q hq delta hd0 hd1 Rstar hRs eps heps heps0' hBoot
  have hq1:q∈Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans cover.dilation_le_one⟩
  have hSmall (y:R3) (hy:y∈cylinder):|referenceRadius delta Rstar p L y| ≤ b/2 :=
    (HG p ((le_max_left _ _).trans hp) q hq1 delta hd0 hd1 Rstar hRs eps heps heps0' y hy
      (hBoot.2 delta ⟨le_rfl,hd1⟩ y hy)).1
  have hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling := by
    intro y hy
    exact ((le_abs_self _).trans (hSmall y hy)).trans_lt ((half_lt_self hb).trans_le (min_le_right _ _))
  refine ⟨hRadius,?_⟩
  intro i u hu hc hSupp
  dsimp only
  have hRoom:∀ y∈tsupport u,‖y-(cover.packet i).y0‖ < (cover.packet i).rho ∧
      |referenceRadius delta Rstar p L y| < di i ∧ referenceRadius delta Rstar p L y≠0 := by
    intro y hy
    have hyRoom:=hSupp hy
    refine ⟨hCenter i y hyRoom.2,?_,(referenceRadius_pos delta Rstar p L y hd0 hRs).ne'⟩
    exact (hSmall y hyRoom.1).trans_lt ((half_lt_self hb).trans_le ((min_le_left _ _).trans (hdAll i)))
  have hGraph:=HD i q hq1 (referenceRadius delta Rstar p L) (contDiff_referenceRadius_actual delta Rstar p L hd0 hRs)
    u hu hc hRoom
  simpa only [nativePacketPhysicalDensityOperator] using hGraph

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
