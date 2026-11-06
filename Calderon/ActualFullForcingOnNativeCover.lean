import Calderon.ActualUpperDensityLateCutoff
import Calderon.ActualUniformFullCutoffCommutator
import Calderon.ActualCenteredNativeCover
import Calderon.ActualUniformScalarCutoffCommutator
import Calderon.ActualEligibleKnownSideFirstJetUniform
import Calderon.ActualCutoffCommutatorSourceRoom
import Calderon.ActualSphereSobolevConstantOne
import Calderon.ActualNativeCutoffHalfLift
import Calderon.ActualFullCutoffCommutatorLateCutoff
import Calderon.ActualNativeCoverConstantForcing
import Calderon.ActualEligibleDensityCutoffPDE

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
open ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
attribute [local irreducible] referenceDensityScalarCutoffCommutator sphereSobolevConstantOne

theorem exists_original_uniform_full_cutoff_commutator_bound_with_late_depth_cutoff_on_native_cover
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (bound separation:ℝ)
    (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∀ cover:NativeNormalCover S L,
      (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) →
      ∃ p0:ℕ,2 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
      ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
      ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 → ∀ tb:ℝ,0 < tb →
      ∀ chi:R3→ℝ,ContDiff ℝ ∞ chi →
      tsupport (fderiv ℝ chi)⊆{y:R3 | y 2 < -(1/4:ℝ)}∪{y:R3 | tb < referenceDepth L y} →
      ∃ lambda0 D:ℝ,0 < lambda0 ∧ lambda0 ≤ cover.dilationCeiling ∧ 1 ≤ D ∧
      ∀ lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      (∀ delta'∈Icc delta (1:ℝ),∀ y∈cylinder,referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
      Nonempty (ConstructedMixedKernel S L lambda delta Rstar bound separation p cover) ∧
      ∀ K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover,
      ∀ Psi:R3→SphereSobolev (3/2:ℝ),ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi →
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      ‖nativeDensityCutoffCommutator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y‖ ≤ D := by
  obtain ⟨lLower,hlLower,HLower⟩ := exists_uniform_scaled_lower_strip S 2 (1/4) (by norm_num) (by norm_num)
  obtain ⟨L0,hL0,HUpper⟩ := exists_original_uniform_upper_eligible_density_first_jets_with_late_depth_cutoff
    hcalc hreg hF hO hD tau0 S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos:0 < L := hL0.trans_le hL
  intro cover hCenter
  obtain ⟨p0,hp0,HP⟩ := HUpper L hL cover
  obtain ⟨Dknown,hDknown,HKnown⟩ := exists_uniform_knownSide_firstJet_bound_any_eligible_native_density
    hcalc hreg hF hO hD tau0 S L cover
  refine ⟨p0,hp0,?_⟩
  intro p hp
  obtain ⟨rDR,hrDR,HDR⟩ := exists_fixed_referenceRadius_spatial_derivative_small_on_cylinder
    S.g1 S.g1_admissible L hLpos p (hp0.trans hp)
  obtain ⟨eps0,heps0,heps01,HE⟩ := HP p hp
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps heps heps0'
  obtain ⟨rUpper,hrUpper,HR⟩ := HE eps heps heps0'
  refine ⟨min rUpper rDR,lt_min hrUpper hrDR,?_⟩
  intro Rstar hRs hRs0 tb htb
  have hRsUpper:Rstar ≤ rUpper := hRs0.trans (min_le_left _ _)
  have hRsDR:Rstar ≤ rDR := hRs0.trans (min_le_right _ _)
  obtain ⟨lUpper,Dupper,hlUpper,hlUpperRoom,hDupper,HJetUpper⟩ := HR Rstar hRs hRsUpper tb htb
  intro chi hchi hDeriv
  let one:=sphereSobolevConstantOne (3/2:ℝ)
  let A:ℝ := max Dknown Dupper
  let C0:ℝ := A+‖one‖+1
  have hEach (i:Fin cover.count) := exists_uniform_referenceDensityScalarCutoffCommutator_bound
    S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo
    (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
    S.g1_admissible hcalc hF hO hD tau0 S.g2 S.g2_admissible hreg chi hchi C0
  choose Ci hCi HComm using hEach
  obtain ⟨Cmax,hCmax⟩ := (Set.finite_range Ci).bddAbove
  let D:ℝ := max Cmax 1
  refine ⟨min lUpper lLower,D,lt_min hlUpper hlLower,(min_le_left _ _).trans hlUpperRoom,le_max_right _ _,?_⟩
  intro lambda hlam hlam0 delta hd hd1 hBoot
  have hlamUpper:lambda ≤ lUpper := hlam0.trans (min_le_left _ _)
  have hlamLower:lambda ≤ lLower := hlam0.trans (min_le_right _ _)
  have hlamRoom:lambda ≤ cover.dilationCeiling := hlamUpper.trans hlUpperRoom
  obtain ⟨hRadius,hKexists,HJetUpper'⟩ := HJetUpper lambda hlam hlamUpper delta hd hd1 hBoot
  have hRadiusCurrent:∀ z∈cylinder,referenceRadius delta Rstar p L z < cover.radiusCeiling :=
    fun z hz => hRadius delta ⟨le_rfl,hd1⟩ z hz
  refine ⟨hRadius,hKexists,?_⟩
  intro K Psi hPsi hPsic hRep i y hy
  have hyC:y∈cylinder := interior_subset hy.1
  have hDR:=HDR Rstar hRs hRsDR delta hd hd1 y hyC
  by_cases hys:y∈tsupport (fderiv ℝ chi)
  · have hField:‖Psi y‖ ≤ A ∧ ‖fderiv ℝ Psi y‖ ≤ A := by
      rcases hDeriv hys with hLow | hUp
      · let U:Set R3 := (interior cylinder∩(cover.packet i).centers)∩{z:R3 | z 2 < -(1/4:ℝ)}
        have hU:IsOpen U := (isOpen_interior.inter (cover.packet i).centers_open).inter
          (isOpen_lt (EuclideanSpace.proj (𝕜:=ℝ) (2:Fin 3)).continuous continuous_const)
        have hKnown:∀ z∈U,lambda • z∈S.W := fun z hz => HLower lambda hlam hlamLower z
          (norm_le_two_of_mem_cylinder z (interior_subset hz.1.1)) hz.2.le
        have h:=HKnown lambda delta Rstar bound separation p K hd hRs hlam hlamRoom hRadiusCurrent
          Psi hPsi hPsic hRep i U hU inter_subset_left hKnown y ⟨hy,hLow⟩
        exact ⟨h.1.trans (le_max_left _ _),(h.2 hDR).trans (le_max_left _ _)⟩
      · let U:Set R3 := (interior cylinder∩(cover.packet i).centers)∩{z:R3 | tb < referenceDepth L z}
        have hU:IsOpen U := (isOpen_interior.inter (cover.packet i).centers_open).inter
          (isOpen_lt continuous_const (contDiff_referenceDepth L).continuous)
        have h:=HJetUpper' K Psi hRep i U hU inter_subset_left (fun z hz => hz.2.le) y ⟨hy,hUp⟩
        exact ⟨h.1.trans (le_max_right _ _),h.2.trans (le_max_right _ _)⟩
    have hSubNorm:‖Psi y-one‖ ≤ C0 := (norm_sub_le _ _).trans (by dsimp only [C0];linarith only [hField.1])
    have hSubDer:fderiv ℝ (fun z => Psi z-one) y=fderiv ℝ Psi y := by
      simpa only [fderiv_const_apply,sub_zero] using fderiv_fun_sub (hPsi.differentiable (by simp) y) (differentiableAt_const one)
    have hSubDerNorm:‖fderiv ℝ (fun z => Psi z-one) y‖ ≤ C0 := by rw [hSubDer];dsimp only [C0];linarith only [hField.2,norm_nonneg one]
    have hPos:=referenceRadius_pos delta Rstar p L y hd hRs
    have hAbs:|referenceRadius delta Rstar p L y| ≤ 4*(cover.packet i).rho := by
      rw [abs_of_pos hPos]
      exact ((hRadiusCurrent y hyC).trans (cover.radius_room i)).le
    have hCb := HComm i lambda ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩ (referenceRadius delta Rstar p L)
      (fun z => Psi z-one) y ((cover.packet i).centers_room y hy.2).1.le
      (hasFDerivAt_referenceRadius delta Rstar p L y hd).differentiableAt hPos.ne' hAbs hDR hSubNorm hSubDerNorm
    dsimp only [nativeDensityCutoffCommutator]
    exact hCb.trans
      ((hCmax (Set.mem_range_self i)).trans (le_max_left _ _))
  · have hzero:=referenceDensityScalarCutoffCommutator_eq_zero_of_notMem_derivative_support
      S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo
      (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
      S.g1_admissible hcalc hF hO hD tau0 S.g2 lambda (referenceRadius delta Rstar p L) chi (fun z => Psi z-one) y hys
    dsimp only [nativeDensityCutoffCommutator]
    rw [hzero,norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
open ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint MetricOperator MetricVolume ActualFiniteHarmonicCore
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL
  referenceDensityScalarCutoffCommutator referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian
  harmonicSphereSubspace sphereSobolevConstantOne nativeNormalizedCutoffPhysicalOperator NativeConstantForcingUniformHalfBound
  nativeDensityCutoffCommutator RepresentsNativeMixedKernelDensity

theorem exists_original_uniform_normalized_cutoff_rhs_half_bound_with_late_depth_cutoff_on_native_cover
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (bound separation:ℝ) (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∀ cover:NativeNormalCover S L,
      (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) →
      ∃ p0:ℕ,2 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
      ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
      ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 → ∀ tb:ℝ,0 < tb →
      ∀ chi:R3→ℝ,ContDiff ℝ ∞ chi → range chi⊆Icc (0:ℝ) 1 →
      tsupport (fderiv ℝ chi)⊆{y:R3 | y 2 < -(1/4:ℝ)}∪{y:R3 | tb < referenceDepth L y} →
      ∃ lambda0 D:ℝ,0 < lambda0 ∧ lambda0 ≤ cover.dilationCeiling ∧ 1 ≤ D ∧
      ∀ lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      (∀ delta'∈Icc delta (1:ℝ),∀ y∈cylinder,referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
      Nonempty (ConstructedMixedKernel S L lambda delta Rstar bound separation p cover) ∧
      ∀ K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover,
      ∀ Psi:R3→SphereSobolev (3/2:ℝ),ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi →
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      ∃ v:SphereSobolev (1/2:ℝ),‖v‖ ≤ D ∧
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v=
        nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y := by
  obtain ⟨L0,hL0,HC⟩ := exists_original_uniform_full_cutoff_commutator_bound_with_late_depth_cutoff_on_native_cover
    hcalc hreg hF hO hD tau0 S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos:0 < L := hL0.trans_le hL
  intro cover hCenter
  obtain ⟨pC,hpC,HP⟩ := HC L hL cover hCenter
  have hConst:NativeConstantForcingUniformHalfBound hcalc hF hO hD tau0 S L cover :=
    nativeConstantForcingUniformHalfBound_of_rho_center_room hcalc hreg hF hO hD tau0 S L hLpos cover hCenter
  obtain ⟨pF,hpF,epsF,hepsF,hepsF1,Dconst,hDconst,HF⟩ := nativeConstantForcingUniformHalfBound_currentBootstrap
    hcalc hF hO hD tau0 S L cover hConst
  refine ⟨max pC pF,hpC.trans (le_max_left _ _),?_⟩
  intro p hp
  have hpC':pC ≤ p := (le_max_left _ _).trans hp
  have hpF':pF ≤ p := (le_max_right _ _).trans hp
  obtain ⟨epsC,hepsC,hepsC1,HE⟩ := HP p hpC'
  refine ⟨min epsC epsF,lt_min hepsC hepsF,(min_le_left _ _).trans hepsC1,?_⟩
  intro eps heps heps0
  have hepsC':eps ≤ epsC := heps0.trans (min_le_left _ _)
  have hepsF':eps ≤ epsF := heps0.trans (min_le_right _ _)
  obtain ⟨R0,hR0,HR⟩ := HE eps heps hepsC'
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRs0 tb htb chi hchi hRange hDeriv
  obtain ⟨lambda0,Dcomm,hlambda0,hlamRoom,hDcomm,HComm⟩ := HR Rstar hRs hRs0 tb htb chi hchi hDeriv
  refine ⟨lambda0,Dconst+Dcomm,hlambda0,hlamRoom,by linarith only [hDconst,hDcomm],?_⟩
  intro lambda hlam hlam0 delta hd hd1 hBoot
  have hOutcome:=HComm lambda hlam hlam0 delta hd hd1 hBoot
  have hRadius:=hOutcome.1
  have hKexists:=hOutcome.2.1
  have HComm':=hOutcome.2.2
  have hRadiusCurrent:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling :=
    fun y hy => hRadius delta ⟨le_rfl,hd1⟩ y hy
  refine ⟨hRadius,hKexists,?_⟩
  intro K Psi hPsi hPsic hRep i y hy
  obtain ⟨v,hv,hvEq⟩ := HF p hpF' lambda ⟨hlam.le,(hlam0.trans hlamRoom).trans cover.dilation_le_one⟩
    delta hd hd1 Rstar hRs eps heps.le hepsF' hBoot i y ⟨interior_subset hy.1,hy.2⟩
  have hchiOne:|chi y| ≤ 1 := by rw [abs_of_nonneg (hRange (Set.mem_range_self y)).1];exact (hRange (Set.mem_range_self y)).2
  exact native_cutoff_rhs_half_lift_of_eligible_density hcalc hreg hF hO hD tau0 hKernel S L lambda delta Rstar
    bound separation p cover K hlam (hlam0.trans hlamRoom) hd hRs hRadiusCurrent Psi hPsi hPsic hRep chi hchi i y hy
    hchiOne Dconst Dcomm v hv hvEq (HComm' K Psi hPsi hPsic hRep i y hy)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
