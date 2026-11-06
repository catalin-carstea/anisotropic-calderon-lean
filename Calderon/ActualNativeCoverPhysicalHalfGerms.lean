import Calderon.ActualLocalPhysicalHalfGraphGerm
import Calderon.ActualRadiusBootstrapSmallJets
import Calderon.ActualCenteredNativeCover
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace

theorem exists_native_cover_uniform_local_physical_half_graph_germs
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      ∀ (u:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ u →
      ∀ i:Fin cover.count,∀ y∈cylinder∩(cover.packet i).centers,
      ∃ W:R3→SphereSobolev (1/2:ℝ),ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
        (fun z => sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (W z))=ᶠ[𝓝 y]
        (fun z => referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi
          (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
          (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
          S.g1_admissible hcalc hF hO hD tau0 S.g2 q (referenceRadius delta Rstar p L)
          (fun t => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u t)) z) := by
  have hEach (i:Fin cover.count) := exists_uniform_radius_local_original_physical_half_graph_germ
    S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo
    (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w
    (cover.packet i).native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 S.g2_admissible hreg hKernel
  choose di hdi HD using hEach
  obtain ⟨d,hd,hdAll⟩ := Geometry.exists_pos_le_finite di hdi
  obtain ⟨pG,hpG,eps0,heps0,heps01,HG⟩ := exists_uniform_referenceRadius_small_ordinary_jets_of_bootstrap
    S.g1 S.g1_admissible cylinder Geometry.isCompact_cylinder L hL (d/2) (half_pos hd)
  refine ⟨max pG 2,le_max_right _ _,eps0,heps0,heps01,?_⟩
  intro p hp q hq delta hd0 hd1 Rstar hRs eps heps heps0' hBoot u hu i y hy
  have hq1:q∈Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans cover.dilation_le_one⟩
  have hpG':pG ≤ p := (le_max_left _ _).trans hp
  have hSmall:=HG p hpG' q hq1 delta hd0 hd1 Rstar hRs eps heps heps0' y hy.1
    (hBoot.2 delta ⟨le_rfl,hd1⟩ y hy.1)
  have hRadius:|referenceRadius delta Rstar p L y| < di i :=
    hSmall.1.trans_lt ((half_lt_self hd).trans_le (hdAll i))
  exact HD i q hq1 (referenceRadius delta Rstar p L)
    (contDiff_referenceRadius_actual delta Rstar p L hd0 hRs) u hu y (hCenter i y hy.2) hRadius
    (referenceRadius_pos delta Rstar p L y hd0 hRs).ne'

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
