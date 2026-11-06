import Calderon.ActualEligibleDensityWholeCoverOutput
import Calderon.ActualUniformCutoffForcingCenteredCover
import Calderon.ActualNativeWeightedCutoffOutput
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore WeightedBaseSpectral
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace
  nativeNormalizedCutoffPhysicalOperator nativePacketPhysicalDensityOperator sphereSobolevConstantOne referenceBaseLift
  RepresentsNativeMixedKernelDensity

theorem exists_original_uniform_genuine_physical_cutoff_output_with_weighted_bound
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (bound separation:ℝ) (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∃ cover:NativeNormalCover S L,
      (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) ∧
      ∀ tb:ℝ,0 < tb → ∃ p0:ℕ,2 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
      ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
      ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 →
      ∀ chi:R3→ℝ,ContDiff ℝ ∞ chi → range chi⊆Icc (0:ℝ) 1 → tsupport chi⊆interior cylinder →
      tsupport (fderiv ℝ chi)⊆{y:R3 | y 2 < -(1/4:ℝ)}∪{y:R3 | tb < referenceDepth L y} →
      ∃ lambda0 D:ℝ,0 < lambda0 ∧ lambda0 ≤ cover.dilationCeiling ∧ 1 ≤ D ∧
      ∀ lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      (∀ delta'∈Icc delta (1:ℝ),∀ y∈cylinder,referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
      Nonempty (ConstructedMixedKernel S L lambda delta Rstar bound separation p cover) ∧
      ∀ K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover,
      ∀ Psi:R3→SphereSobolev (3/2:ℝ),ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi →
      ∃ (W:R3→SphereL2) (hW:ContDiff ℝ ∞ W) (hWc:HasCompactSupport W),tsupport W⊆tsupport chi ∧
        (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (W y))=
          nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y) ∧
        ‖referenceBaseLift S.g1 S.g1_admissible L lambda W hW.continuous hWc‖ ≤ D := by
  obtain ⟨L0,hL0,H0⟩ := exists_original_uniform_normalized_cutoff_rhs_half_bound_with_center_room
    hcalc hreg hF hO hD tau0 hKernel S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos:0 < L := hL0.trans_le hL
  obtain ⟨cover,hCenter,HTB⟩ := H0 L hL
  obtain ⟨pG,hpG,eG,heG,heG1,HG⟩ := exists_uniform_original_eligible_density_whole_cover_physical_output
    hcalc hreg hF hO hD tau0 hKernel S L hLpos cover hCenter
  obtain ⟨C,hC,HC⟩ := exists_uniform_original_weighted_cutoff_output_budget hcalc hF hO hD tau0 S L cover
  refine ⟨cover,hCenter,?_⟩
  intro tb htb
  obtain ⟨pF,hpF,HF⟩ := HTB tb htb
  refine ⟨max pF pG,hpF.trans (le_max_left _ _),?_⟩
  intro p hp
  have hpF':pF ≤ p := (le_max_left _ _).trans hp
  have hpG':pG ≤ p := (le_max_right _ _).trans hp
  obtain ⟨eF,heF,heF1,HE⟩ := HF p hpF'
  refine ⟨min eF eG,lt_min heF heG,(min_le_left _ _).trans heF1,?_⟩
  intro eps heps heps0
  have heF':eps ≤ eF := heps0.trans (min_le_left _ _)
  have heG':eps ≤ eG := heps0.trans (min_le_right _ _)
  have hRadiusChoice:=HE eps heps heF'
  let R0:ℝ := Classical.choose hRadiusChoice
  have hRadiusData:=Classical.choose_spec hRadiusChoice
  have hR0:0 < R0 := hRadiusData.1
  have HR:=hRadiusData.2
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRs0 chi hchi hRange hSupp hDeriv
  have hchic:HasCompactSupport chi := Geometry.isCompact_cylinder.of_isClosed_subset
    (isClosed_tsupport chi) (hSupp.trans interior_subset)
  have hScaleChoice:=HR Rstar hRs hRs0 chi hchi hRange hDeriv
  let lambda0:ℝ := Classical.choose hScaleChoice
  have hDChoice:=Classical.choose_spec hScaleChoice
  let Dhalf:ℝ := Classical.choose hDChoice
  have hScaleData:=Classical.choose_spec hDChoice
  have hlam0:0 < lambda0 := hScaleData.1
  have hlamRoom:lambda0 ≤ cover.dilationCeiling := hScaleData.2.1
  have hDhalf:1 ≤ Dhalf := hScaleData.2.2.1
  have HHalf:=hScaleData.2.2.2
  have hD:1 ≤ C*Dhalf := by
    have h:=mul_le_mul hC hDhalf (by norm_num:0 ≤ (1:ℝ)) (zero_le_one.trans hC)
    simpa only [one_mul] using h
  refine ⟨lambda0,C*Dhalf,hlam0,hlamRoom,hD,?_⟩
  intro lambda hlam hlam0' delta hd hd1 hBoot
  have hOutcome:=HHalf lambda hlam hlam0' delta hd hd1 hBoot
  have hRadius:=hOutcome.1
  have hKexists:=hOutcome.2.1
  have HHalf':=hOutcome.2.2
  refine ⟨hRadius,hKexists,?_⟩
  intro K Psi hPsi hPsic hRep
  have hOutputChoice:=HG p hpG' lambda hlam (hlam0'.trans hlamRoom) delta hd hd1 Rstar hRs
    eps heps.le heG' hBoot (fun y hy => hRadius delta ⟨le_rfl,hd1⟩ y hy) bound separation K Psi hPsi hPsic hRep
    chi hchi hchic hSupp
  let W:R3→SphereL2 := Classical.choose hOutputChoice
  have hOutputData:=Classical.choose_spec hOutputChoice
  have hW:ContDiff ℝ ∞ W := hOutputData.1
  have hWc:HasCompactSupport W := hOutputData.2.1
  have hWSupp:tsupport W⊆tsupport chi := hOutputData.2.2.1
  have hGraph:=hOutputData.2.2.2
  have hNorm:=HC chi hSupp lambda ⟨hlam.le,((hlam0'.trans hlamRoom).trans cover.dilation_le_one)⟩
    delta Rstar p Psi W hW.continuous hWc hWSupp Dhalf (zero_le_one.trans hDhalf)
    (HHalf' K Psi hPsi hPsic hRep) hGraph
  exact ⟨W,hW,hWc,hWSupp,hGraph,hNorm⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
