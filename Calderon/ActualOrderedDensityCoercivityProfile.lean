import Calderon.ActualReferenceBetaRadiusBudget
import Calderon.ActualReferenceBetaRadiusScale
import Calderon.ActualUniformFiniteGraphLateCutoff
import Calderon.ActualUniformDensityFromFinitePhysicalCoercivity
import Calderon.ActualFinitePhysicalCoercivityDensityConsumer
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ActualFiniteHarmonicCore WeightedBaseSpectral ReferenceDensityBounds
  SpectralCoreRegularity SpectralWeightedGraph SphereHilbertDecomposition EnergyBridge DirichletFamily ActualHigherRadiusProfile RadiusProfile ReferenceWeightedApproximation
  DirichletFamily.DriftBootstrap ConformalDepth ActualScalarPrincipalAdjoint
attribute [local irreducible] nativeDensitySphereL2L sphereSobolevInclusionL sphereSobolevPartialSumL
  harmonicSphereSubspace finiteCoreSobolevLift nativePacketPhysicalDensityOperator referenceBaseLift
  sphereSobolevConstantOne nativeNormalizedCutoffPhysicalOperator RepresentsNativeMixedKernelDensity

private lemma exists_original_normalized_fiveHalf_source_lift_ordered_profile
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar bound separation:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover)
    (hd:0 < delta) (hRs:0 < Rstar) (hlam:0 < lambda) (hlamRoom:lambda ≤ cover.dilationCeiling)
    (hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi) (hPsic:HasCompactSupport Psi)
    (hRep:RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi)
    (chi:R3→ℝ) (hchi:ContDiff ℝ ∞ chi) (hchic:HasCompactSupport chi) (hSupp:tsupport chi⊆interior cylinder):
    ∃ U5:R3→SphereSobolev (5/2:ℝ),ContDiff ℝ ∞ U5 ∧ HasCompactSupport U5 ∧
      (fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U5 y))=normalizedThreeHalfSourceField chi Psi := by
  unfold RepresentsNativeMixedKernelDensity at hRep
  have hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  obtain ⟨Psi5,hPsi5,hPsi5c,hInc,hSame⟩ := exists_fiveHalf_lift_of_eligible_native_density
    hcalc hreg hF hO hD tau0 S L lambda delta Rstar bound separation p cover K hd hRs hLam hRadius
    Psi hPsi hPsic hRep chi hSupp
  have hMean0 := (sphereMean_any_eligible_native_density_and_cutoff_sub_one hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar bound separation p cover K hd hRs hlam hlamRoom hRadius Psi hPsi hPsic hRep chi hSupp).2
  have hProps:=normalizedFiveHalfSourceField_properties hO hD chi hchi hchic hSupp Psi Psi5 hPsi5 hInc hMean0
  exact ⟨normalizedFiveHalfSourceField chi Psi5,hProps.1,hProps.2.1,hProps.2.2.1⟩

theorem exists_original_ordered_density_coercivity_profile
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (bound separation:ℝ) (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∃ cover:NativeNormalCover S L,
      (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) ∧
      ∃ p0:ℕ,24 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
      ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
      ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 →
      ∃ etaKernel:ℝ,0 < etaKernel ∧ etaKernel ≤ cover.dilationCeiling ∧
      (∀ lambda∈Icc (0:ℝ) 1,∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ y∈cylinder,
        referenceRadius delta Rstar p L y*(actualReferenceBeta S.g1 L lambda delta Rstar p y)^2 ≤ eps) ∧
      (∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ y∈cylinder,
        referenceRadius delta Rstar p L y < cover.radiusCeiling) ∧
      (∀ lambda:ℝ,0 < lambda → lambda ≤ etaKernel → ∀ delta:ℝ,0 < delta → delta ≤ 1 →
        CurrentRadiusBootstrap S L lambda delta Rstar eps p →
        Nonempty (ConstructedMixedKernel S L lambda delta Rstar bound separation p cover)) ∧
      ∀ tb:ℝ,0 < tb →
      ∀ (chi:R3→ℝ) (hchi:ContDiff ℝ ∞ chi), range chi⊆Icc (0:ℝ) 1 → ∀ hSupp:tsupport chi⊆interior cylinder,
      tsupport (fderiv ℝ chi)⊆{y:R3 | y 2 < -(1/4:ℝ)}∪{y:R3 | tb < referenceDepth L y} →
      ∀ (c lambdaC:ℝ),0 < c → 0 < lambdaC →
      (∀ lambda:ℝ,0 < lambda → lambda ≤ lambdaC → ∀ delta:ℝ,0 < delta → delta ≤ 1 →
        CurrentRadiusBootstrap S L lambda delta Rstar eps p →
        NativeFinitePhysicalCoerciveBound hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p c) →
      ∃ lambda0 D:ℝ,0 < lambda0 ∧ lambda0 ≤ cover.dilationCeiling ∧ 1 ≤ D ∧
      ∀ lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      (∀ delta'∈Icc delta (1:ℝ),∀ y∈cylinder,referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
      Nonempty (ConstructedMixedKernel S L lambda delta Rstar bound separation p cover) ∧
      ∀ K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover,
      ∀ (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi),HasCompactSupport Psi →
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi →
      ‖referenceBaseLift S.g1 S.g1_admissible L lambda (fun y => chi y • nativeDensitySphereL2L hO hD (Psi y))
        (hchi.continuous.smul ((nativeDensitySphereL2L hO hD).continuous.comp hPsi.continuous))
        (show HasCompactSupport chi from Geometry.isCompact_cylinder.of_isClosed_subset (isClosed_tsupport chi) (hSupp.trans interior_subset)).smul_right‖ ≤ D := by
  obtain ⟨L0,hL0,H0⟩ := exists_original_uniform_finite_physical_cutoff_graph_with_late_depth_cutoff
    hcalc hreg hF hO hD tau0 hKernel S bound separation hBound hSep
  refine Exists.intro L0 ?_
  refine And.intro hL0 ?_
  intro L hL
  obtain ⟨cover,hCenter,HTB⟩ := H0 L hL
  have hLpos:0 < L := hL0.trans_le hL
  obtain ⟨pBeta,_hpBeta,HBetaP⟩ :=
    exists_uniform_actual_beta_radius_budget_on_native_cover S L hLpos cover
  have hCChoice:=exists_original_density_norm_bound_of_actual_finite_physical_graph hcalc hF hO hD tau0 S L cover
  let C:ℝ := Classical.choose hCChoice
  have hCData:=Classical.choose_spec hCChoice
  have hC:0 < C := hCData.1
  have HC:=hCData.2
  refine Exists.intro cover ?_
  refine And.intro hCenter ?_
  have hPChoice:=HTB
  let p0:ℕ := Classical.choose hPChoice
  have hPData:=Classical.choose_spec hPChoice
  have hp0:2 ≤ p0 := hPData.1
  have HP:=hPData.2
  refine Exists.intro (max 24 (max p0 pBeta)) ?_
  refine And.intro (le_max_left _ _) ?_
  intro p hp
  have hpNative:p0 ≤ p := (le_max_left _ _).trans ((le_max_right _ _).trans hp)
  have hpBeta:pBeta ≤ p := (le_max_right _ _).trans ((le_max_right _ _).trans hp)
  have hEChoice:=HP p hpNative
  let eps0:ℝ := Classical.choose hEChoice
  have hEData:=Classical.choose_spec hEChoice
  have heps0:0 < eps0 := hEData.1
  have heps01:eps0 ≤ 1 := hEData.2.1
  have HE:=hEData.2.2
  refine Exists.intro eps0 ?_
  refine And.intro heps0 ?_
  refine And.intro heps01 ?_
  intro eps heps heps0'
  have hRChoice:=HE eps heps heps0'
  let R0:ℝ := Classical.choose hRChoice
  have hRData:=Classical.choose_spec hRChoice
  have hR0:0 < R0 := hRData.1
  have HR:=hRData.2
  have hBetaScaleChoice:=HBetaP p hpBeta eps heps
  let RB:ℝ := Classical.choose hBetaScaleChoice
  have hBetaScaleData:=Classical.choose_spec hBetaScaleChoice
  have hRB:0 < RB := hBetaScaleData.1
  have HBeta:=hBetaScaleData.2
  refine Exists.intro (min R0 RB) ?_
  refine And.intro (lt_min hR0 hRB) ?_
  intro Rstar hRs hRs0
  have hRsNative:Rstar ≤ R0 := hRs0.trans (min_le_left _ _)
  have hRsBeta:Rstar ≤ RB := hRs0.trans (min_le_right _ _)
  have hBetaData:=HBeta Rstar hRs hRsBeta
  have hBeta:=hBetaData.1
  have hRoom:=hBetaData.2
  have hZeroRange:range (fun _:R3 => (0:ℝ))⊆Icc (0:ℝ) 1 := by
    rintro x ⟨z,rfl⟩
    constructor <;> norm_num
  have hZeroSupport:tsupport (fun _:R3 => (0:ℝ))⊆interior cylinder := by simp
  have hZeroDeriv:tsupport (fderiv ℝ (fun _:R3 => (0:ℝ)))⊆
      {y:R3 | y 2 < -(1/4:ℝ)}∪{y:R3 | (1:ℝ) < referenceDepth L y} := by simp
  have hKernelScaleChoice:=HR Rstar hRs hRsNative 1 (by norm_num) (fun _:R3 => (0:ℝ))
    contDiff_const hZeroRange hZeroSupport hZeroDeriv
  let etaKernel:ℝ := Classical.choose hKernelScaleChoice
  have hKernelDChoice:=Classical.choose_spec hKernelScaleChoice
  let DKernel:ℝ := Classical.choose hKernelDChoice
  have hKernelData:=Classical.choose_spec hKernelDChoice
  have hEtaKernel:0 < etaKernel := hKernelData.1
  have hEtaKernelRoom:etaKernel ≤ cover.dilationCeiling := hKernelData.2.1
  have HKernel:=hKernelData.2.2.2
  have hKK:∀ lambda:ℝ,0 < lambda → lambda ≤ etaKernel → ∀ delta:ℝ,0 < delta → delta ≤ 1 →
      CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      Nonempty (ConstructedMixedKernel S L lambda delta Rstar bound separation p cover) := by
    intro lambda hlam hlamK delta hd hd1 hBoot
    exact (HKernel lambda hlam hlamK delta hd hd1 hBoot).2.1
  refine Exists.intro etaKernel ?_
  refine And.intro hEtaKernel ?_
  refine And.intro hEtaKernelRoom ?_
  refine And.intro hBeta ?_
  refine And.intro hRoom ?_
  refine And.intro hKK ?_
  intro tb htb chi hchi hRange hSupp hDeriv c lambdaC hc hlamC hCoercive
  have hchic:HasCompactSupport chi := Geometry.isCompact_cylinder.of_isClosed_subset
    (isClosed_tsupport chi) (hSupp.trans interior_subset)
  have hScaleChoice:=HR Rstar hRs hRsNative tb htb chi hchi hRange hSupp hDeriv
  let lambdaG:ℝ := Classical.choose hScaleChoice
  have hDChoice:=Classical.choose_spec hScaleChoice
  let Dgraph:ℝ := Classical.choose hDChoice
  have hScaleData:=Classical.choose_spec hDChoice
  have hlamG:0 < lambdaG := hScaleData.1
  have hGRoom:lambdaG ≤ cover.dilationCeiling := hScaleData.2.1
  have hDgraph:1 ≤ Dgraph := hScaleData.2.2.1
  have HG:=hScaleData.2.2.2
  refine ⟨min lambdaG lambdaC,max (Dgraph/Real.sqrt c+C) 1,lt_min hlamG hlamC,
    (min_le_left _ _).trans hGRoom,le_max_right _ _,?_⟩
  intro lambda hlam hlam0 delta hd hd1 hBoot
  have hlamG':lambda ≤ lambdaG := hlam0.trans (min_le_left _ _)
  have hlamC':lambda ≤ lambdaC := hlam0.trans (min_le_right _ _)
  have hOutcome:=HG lambda hlam hlamG' delta hd hd1 hBoot
  have hRadius:=hOutcome.1
  have hKexists:=hOutcome.2.1
  have HGraph:=hOutcome.2.2
  refine ⟨hRadius,hKexists,?_⟩
  intro K Psi hPsi hPsic hRep
  have hGraphChoice:=HGraph K Psi hPsi hPsic hRep
  have hCore:=hGraphChoice.1
  let F:ℕ→R3→SphereL2 := Classical.choose hGraphChoice.2
  have hFChoice:=Classical.choose_spec hGraphChoice.2
  let f:R3→SphereL2 := Classical.choose hFChoice
  have hFDataChoice:=Classical.choose_spec hFChoice
  have hFData:=hFDataChoice.1
  let hf:ContDiff ℝ ∞ f := Classical.choose hFDataChoice.2
  have hfcChoice:=Classical.choose_spec hFDataChoice.2
  let hfc:HasCompactSupport f := Classical.choose hfcChoice
  have hGraphData:=Classical.choose_spec hfcChoice
  have hOutput:=hGraphData.2.2.1
  have hNorm:=hGraphData.2.2.2
  have hLiftChoice:= exists_original_normalized_fiveHalf_source_lift_ordered_profile hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar bound separation p cover K hd hRs hlam (hlamG'.trans hGRoom)
    (fun y hy => hRadius delta ⟨le_rfl,hd1⟩ y hy) Psi hPsi hPsic hRep chi hchi hchic hSupp
  let U5:R3→SphereSobolev (5/2:ℝ) := Classical.choose hLiftChoice
  have hLiftData:=Classical.choose_spec hLiftChoice
  have hU5:ContDiff ℝ ∞ U5 := hLiftData.1
  have hU5c:HasCompactSupport U5 := hLiftData.2.1
  have hEq:=hLiftData.2.2
  have hFinite:=hCoercive lambda hlam hlamC' delta hd hd1 hBoot
  unfold NativeFinitePhysicalCoerciveBound at hFinite
  have hDensity:=HC lambda ⟨hlam.le,hlamG'.trans hGRoom⟩ delta Rstar c Dgraph p hc chi hchi hchic hSupp hRange
    Psi hPsi U5 hU5 hU5c hEq F f hf hfc hNorm hOutput hCore hFData hFinite
  exact hDensity.trans (le_max_left _ _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
