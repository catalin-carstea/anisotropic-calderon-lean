import Calderon.InjectiveSmoothLocalLiftGluing
import Calderon.ActualNativeCoverPhysicalHalfGerms
import Calderon.ActualPacketPhysicalOperatorCoherence
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace

theorem exists_native_cover_uniform_global_physical_half_output
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      ∀ (u:R3→SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u⊆interior cylinder →
      ∃ W:R3→SphereSobolev (1/2:ℝ),ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W⊆tsupport u ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (W y)=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (fun t => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u t)) i y := by
  obtain ⟨pG,hpG,eG,heG,heG1,HG⟩ := exists_native_cover_uniform_local_physical_half_graph_germs
    hcalc hreg hF hO hD tau0 hKernel S L hL cover hCenter
  obtain ⟨pR,hpR,eR,heR,heR1,HR⟩ := exists_uniform_referenceRadius_small_ordinary_jets_of_bootstrap
    S.g1 S.g1_admissible cylinder Geometry.isCompact_cylinder L hL (cover.radiusCeiling/2) (half_pos cover.radius_positive)
  refine ⟨max pG pR,hpG.trans (le_max_left _ _),min eG eR,lt_min heG heR,(min_le_left _ _).trans heG1,?_⟩
  intro p hp q hq delta hd hd1 Rstar hRs eps heps heps0 hBoot u hu huc hSupport
  have hpG':pG ≤ p := (le_max_left _ _).trans hp
  have hpR':pR ≤ p := (le_max_right _ _).trans hp
  have heG':eps ≤ eG := heps0.trans (min_le_left _ _)
  have heR':eps ≤ eR := heps0.trans (min_le_right _ _)
  have hq1:q∈Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans cover.dilation_le_one⟩
  have hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling := by
    intro y hy
    have h:=HR p hpR' q hq1 delta hd hd1 Rstar hRs eps heps heR' y hy (hBoot.2 delta ⟨le_rfl,hd1⟩ y hy)
    exact ((le_abs_self _).trans h.1).trans_lt (half_lt_self cover.radius_positive)
  let I:=sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let V:R3→SphereSobolev (3/2:ℝ) := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (u y)
  have hV:ContDiff ℝ ∞ V := (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hu
  let U:Fin cover.count→Set R3 := fun i => interior cylinder∩(cover.packet i).centers
  let F:Fin cover.count→R3→SphereSobolev (-(1/2:ℝ)) := fun i y =>
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p V i y
  have hU:∀ i,IsOpen (U i) := fun i => isOpen_interior.inter (cover.packet i).centers_open
  have hCover:∀ y∈tsupport u,∃ i,y∈U i := by
    intro y hy
    obtain ⟨i,hi⟩ := cover.covers_cylinder y (interior_subset (hSupport hy))
    exact ⟨i,hSupport hy,hi⟩
  apply exists_smooth_compact_injective_lift_of_compatible_local_germs I
    (sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) (tsupport u) huc U hU hCover F
  · intro i j y hy
    exact nativePacketPhysicalDensityOperator_eq_on_overlap hcalc hreg hF hO hD tau0 hKernel
      S L q delta Rstar p cover hd hRs hq i j y ⟨hy.1.2,hy.2.2⟩
      (hRadius y (interior_subset hy.1.1)) V hV
  · intro i y hy
    have hLowSupp:tsupport V⊆tsupport u := tsupport_comp_subset
      (map_zero (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) u
    have hFSupp:tsupport (F i)⊆tsupport u := by
      dsimp only [F,nativePacketPhysicalDensityOperator]
      exact (tsupport_referencePhysicalDensityOperator_subset S.g1 L (cover.packet i).y0 (cover.packet i).Phi
        (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
        (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
        S.g1_admissible hcalc hF hO hD tau0 S.g2 q (referenceRadius delta Rstar p L) V).trans hLowSupp
    exact image_eq_zero_of_notMem_tsupport (fun hz => hy (hFSupp hz))
  · intro i y hy
    obtain ⟨w,hw,hwc,hEq⟩ := HG p hpG' q hq delta hd hd1 Rstar hRs eps heps heG' hBoot u hu i y
      ⟨interior_subset hy.1,hy.2⟩
    refine ⟨w,hw,?_⟩
    simpa only [I,F,nativePacketPhysicalDensityOperator,V] using hEq

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
