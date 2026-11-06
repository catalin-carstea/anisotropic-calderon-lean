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
open ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint MetricOperator MetricVolume ActualFiniteHarmonicCore
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL
  referenceDensityScalarCutoffCommutator referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian
  harmonicSphereSubspace sphereSobolevConstantOne nativeNormalizedCutoffPhysicalOperator NativeConstantForcingUniformHalfBound
  nativeDensityCutoffCommutator RepresentsNativeMixedKernelDensity

theorem exists_original_uniform_normalized_cutoff_rhs_half_bound_with_late_depth_cutoff
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (bound separation:ℝ) (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∃ cover:NativeNormalCover S L,
      (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) ∧
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
  obtain ⟨L0,hL0,HC⟩ := exists_original_uniform_full_cutoff_commutator_bound_with_late_depth_cutoff
    hcalc hreg hF hO hD tau0 S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos:0 < L := hL0.trans_le hL
  obtain ⟨cover,hCenter,pC,hpC,HP⟩ := HC L hL
  have hConst:NativeConstantForcingUniformHalfBound hcalc hF hO hD tau0 S L cover :=
    nativeConstantForcingUniformHalfBound_of_rho_center_room hcalc hreg hF hO hD tau0 S L hLpos cover hCenter
  obtain ⟨pF,hpF,epsF,hepsF,hepsF1,Dconst,hDconst,HF⟩ := nativeConstantForcingUniformHalfBound_currentBootstrap
    hcalc hF hO hD tau0 S L cover hConst
  refine ⟨cover,hCenter,max pC pF,hpC.trans (le_max_left _ _),?_⟩
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
