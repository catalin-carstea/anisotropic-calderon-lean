import Calderon.ActualEligibleDensityWholeFiniteGraph
import Calderon.ActualUniformCutoffForcingCenteredCover
import Calderon.ActualUniformGenuinePhysicalCutoffOutput
import Calderon.ActualWholeCoverPhysicalOutputUniqueness
import Calderon.ActualNativeWeightedCutoffOutput
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ConformalDepth ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore WeightedBaseSpectral
  SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph PositiveSpectralCore
attribute [local irreducible] sphereSobolevInclusionL referencePhysicalDensityOperator harmonicSphereSubspace
  nativeNormalizedCutoffPhysicalOperator nativePacketPhysicalDensityOperator sphereSobolevConstantOne referenceBaseLift
  RepresentsNativeMixedKernelDensity

theorem exists_original_uniform_finite_physical_cutoff_graph_with_weighted_bound
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
      (∀ n:ℕ,∃ A:smoothCompactFiniteSphereCore hO hD,
        (∀ y:R3,finiteCoreSobolevLift hO hD (3/2:ℝ) A y=
          sphereSobolevPartialSumL (3/2:ℝ) n (normalizedThreeHalfSourceField chi Psi y)) ∧
        tsupport (A:R3→SphereL2)⊆tsupport chi ∧ ∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) ∧
      ∃ (F:ℕ→R3→SphereL2) (f:R3→SphereL2),
      (∀ n:ℕ,ContDiff ℝ ∞ (F n) ∧ HasCompactSupport (F n) ∧ tsupport (F n)⊆tsupport chi ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F n y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
            (fun z => sphereSobolevPartialSumL (3/2:ℝ) n (normalizedThreeHalfSourceField chi Psi z)) i y) ∧
      ∃ (hf:ContDiff ℝ ∞ f) (hfc:HasCompactSupport f),tsupport f⊆tsupport chi ∧
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
          nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y) ∧
      Tendsto (fun n:ℕ => ∫ y,ReferenceDensityBounds.referenceDensityFamily S.g1 L (lambda,y)*‖F n y-f y‖^2) atTop (𝓝 0) ∧
      ‖referenceBaseLift S.g1 S.g1_admissible L lambda f hf.continuous hfc‖ ≤ D := by
  obtain ⟨L0,hL0,H0⟩ := exists_original_uniform_genuine_physical_cutoff_output_with_weighted_bound
    hcalc hreg hF hO hD tau0 hKernel S bound separation hBound hSep
  refine Exists.intro L0 ?_
  refine And.intro hL0 ?_
  intro L hL
  have hLpos:0 < L := hL0.trans_le hL
  obtain ⟨cover,hCenter,HTB⟩ := H0 L hL
  have hGraphThresholdChoice:=exists_uniform_original_eligible_density_whole_finite_physical_graph
    hcalc hreg hF hO hD tau0 hKernel S L hLpos cover hCenter
  let pG:ℕ := Classical.choose hGraphThresholdChoice
  have hPData:=Classical.choose_spec hGraphThresholdChoice
  have hpG:2 ≤ pG := hPData.1
  let eG:ℝ := Classical.choose hPData.2
  have hEData:=Classical.choose_spec hPData.2
  have heG:0 < eG := hEData.1
  have heG1:eG ≤ 1 := hEData.2.1
  have HG:=hEData.2.2
  refine Exists.intro cover ?_
  refine And.intro hCenter ?_
  intro tb htb
  have hPChoice:=HTB tb htb
  let pF:ℕ := Classical.choose hPChoice
  have hPFData:=Classical.choose_spec hPChoice
  have hpF:2 ≤ pF := hPFData.1
  have HF:=hPFData.2
  refine Exists.intro (max pF pG) ?_
  refine And.intro (hpF.trans (le_max_left _ _)) ?_
  intro p hp
  have hpF':pF ≤ p := (le_max_left _ _).trans hp
  have hpG':pG ≤ p := (le_max_right _ _).trans hp
  have hEFChoice:=HF p hpF'
  let eF:ℝ := Classical.choose hEFChoice
  have hEFData:=Classical.choose_spec hEFChoice
  have heF:0 < eF := hEFData.1
  have heF1:eF ≤ 1 := hEFData.2.1
  have HE:=hEFData.2.2
  refine Exists.intro (min eF eG) ?_
  refine And.intro (lt_min heF heG) ?_
  refine And.intro ((min_le_left _ _).trans heF1) ?_
  intro eps heps heps0
  have heF':eps ≤ eF := heps0.trans (min_le_left _ _)
  have heG':eps ≤ eG := heps0.trans (min_le_right _ _)
  have hRadiusChoice:=HE eps heps heF'
  let R0:ℝ := Classical.choose hRadiusChoice
  have hRadiusData:=Classical.choose_spec hRadiusChoice
  have hR0:0 < R0 := hRadiusData.1
  have HR:=hRadiusData.2
  refine Exists.intro R0 ?_
  refine And.intro hR0 ?_
  intro Rstar hRs hRs0 chi hchi hRange hSupp hDeriv
  have hchic:HasCompactSupport chi := Geometry.isCompact_cylinder.of_isClosed_subset
    (isClosed_tsupport chi) (hSupp.trans interior_subset)
  have hScaleChoice:=HR Rstar hRs hRs0 chi hchi hRange hSupp hDeriv
  let lambda0:ℝ := Classical.choose hScaleChoice
  have hDChoice:=Classical.choose_spec hScaleChoice
  let D:ℝ := Classical.choose hDChoice
  have hScaleData:=Classical.choose_spec hDChoice
  have hlam0:0 < lambda0 := hScaleData.1
  have hlamRoom:lambda0 ≤ cover.dilationCeiling := hScaleData.2.1
  have hDLower:1 ≤ D := hScaleData.2.2.1
  have HFull:=hScaleData.2.2.2
  refine Exists.intro lambda0 ?_
  refine Exists.intro D ?_
  refine And.intro hlam0 ?_
  refine And.intro hlamRoom ?_
  refine And.intro hDLower ?_
  intro lambda hlam hlam0' delta hd hd1 hBoot
  have hOutcome:=HFull lambda hlam hlam0' delta hd hd1 hBoot
  have hRadius:=hOutcome.1
  have hKexists:=hOutcome.2.1
  have HOutput:=hOutcome.2.2
  refine ⟨hRadius,hKexists,?_⟩
  intro K Psi hPsi hPsic hRep
  have hGraphChoice:=HG p hpG' lambda hlam (hlam0'.trans hlamRoom) delta hd hd1 Rstar hRs
    eps heps.le heG' hBoot (fun y hy => hRadius delta ⟨le_rfl,hd1⟩ y hy) bound separation K Psi hPsi hPsic hRep
    chi hchi hchic hSupp
  have hCore:=hGraphChoice.1
  let F:ℕ→R3→SphereL2 := Classical.choose hGraphChoice.2
  have hFChoice:=Classical.choose_spec hGraphChoice.2
  let f:R3→SphereL2 := Classical.choose hFChoice
  have hGraphData:=Classical.choose_spec hFChoice
  have hf:ContDiff ℝ ∞ f := hGraphData.2.1
  have hfc:HasCompactSupport f := hGraphData.2.2.1
  have hfSupp:tsupport f⊆tsupport chi := hGraphData.2.2.2.1
  have hfGraph:=hGraphData.2.2.2.2.1
  have hOriginalChoice:=HOutput K Psi hPsi hPsic hRep
  let W:R3→SphereL2 := Classical.choose hOriginalChoice
  have hWChoice:=Classical.choose_spec hOriginalChoice
  let hW:ContDiff ℝ ∞ W := Classical.choose hWChoice
  have hWcChoice:=Classical.choose_spec hWChoice
  let hWc:HasCompactSupport W := Classical.choose hWcChoice
  have hOriginalData:=Classical.choose_spec hWcChoice
  have hWSupp:tsupport W⊆tsupport chi := hOriginalData.1
  have hWGraph:=hOriginalData.2.1
  have hWNorm:=hOriginalData.2.2
  have hSame:f=W := eq_of_same_native_cover_negative_graph hO hD S L cover (tsupport chi) hSupp
    f W hfSupp hWSupp (fun i y => nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y)
    hfGraph hWGraph
  have hNorm:‖referenceBaseLift S.g1 S.g1_admissible L lambda f hf.continuous hfc‖ ≤ D := by
    simpa only [hSame] using hWNorm
  exact ⟨hCore,F,f,hGraphData.1,hf,hfc,hfSupp,hfGraph,hGraphData.2.2.2.2.2,hNorm⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
