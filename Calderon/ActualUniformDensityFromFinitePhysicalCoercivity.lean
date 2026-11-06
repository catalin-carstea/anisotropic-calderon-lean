import Calderon.ActualUniformFinitePhysicalCutoffGraph
import Calderon.ActualFinitePhysicalCoercivityDensityConsumer
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ActualFiniteHarmonicCore WeightedBaseSpectral ReferenceDensityBounds
  SpectralCoreRegularity SpectralWeightedGraph SphereHilbertDecomposition EnergyBridge DirichletFamily
  DirichletFamily.DriftBootstrap ConformalDepth ActualScalarPrincipalAdjoint
attribute [local irreducible] nativeDensitySphereL2L sphereSobolevInclusionL sphereSobolevPartialSumL
  harmonicSphereSubspace finiteCoreSobolevLift nativePacketPhysicalDensityOperator referenceBaseLift
  sphereSobolevConstantOne nativeNormalizedCutoffPhysicalOperator RepresentsNativeMixedKernelDensity

def NativeFinitePhysicalCoerciveBound
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (chi:R3→ℝ) (q delta Rstar:ℝ) (p:ℕ) (c:ℝ):Prop :=
  ∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      ∀ V:R3→SphereL2,ContDiff ℝ ∞ V → HasCompactSupport V → tsupport V⊆tsupport chi →
      (∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y) →
      c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖(A:R3→SphereL2) y‖^2) ≤
        ∫ y,referenceDensityFamily S.g1 L (q,y)*‖V y‖^2

private lemma exists_original_normalized_fiveHalf_source_lift
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

theorem exists_original_uniform_density_bound_of_finite_physical_coercivity
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
  obtain ⟨L0,hL0,H0⟩ := exists_original_uniform_finite_physical_cutoff_graph_with_weighted_bound
    hcalc hreg hF hO hD tau0 hKernel S bound separation hBound hSep
  refine Exists.intro L0 ?_
  refine And.intro hL0 ?_
  intro L hL
  obtain ⟨cover,hCenter,HTB⟩ := H0 L hL
  have hCChoice:=exists_original_density_norm_bound_of_actual_finite_physical_graph hcalc hF hO hD tau0 S L cover
  let C:ℝ := Classical.choose hCChoice
  have hCData:=Classical.choose_spec hCChoice
  have hC:0 < C := hCData.1
  have HC:=hCData.2
  refine Exists.intro cover ?_
  refine And.intro hCenter ?_
  intro tb htb
  have hPChoice:=HTB tb htb
  let p0:ℕ := Classical.choose hPChoice
  have hPData:=Classical.choose_spec hPChoice
  have hp0:2 ≤ p0 := hPData.1
  have HP:=hPData.2
  refine Exists.intro p0 ?_
  refine And.intro hp0 ?_
  intro p hp
  have hEChoice:=HP p hp
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
  refine Exists.intro R0 ?_
  refine And.intro hR0 ?_
  intro Rstar hRs hRs0 chi hchi hRange hSupp hDeriv c lambdaC hc hlamC hCoercive
  have hchic:HasCompactSupport chi := Geometry.isCompact_cylinder.of_isClosed_subset
    (isClosed_tsupport chi) (hSupp.trans interior_subset)
  have hScaleChoice:=HR Rstar hRs hRs0 chi hchi hRange hSupp hDeriv
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
  obtain ⟨U5,hU5,hU5c,hEq⟩ := exists_original_normalized_fiveHalf_source_lift hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar bound separation p cover K hd hRs hlam (hlamG'.trans hGRoom)
    (fun y hy => hRadius delta ⟨le_rfl,hd1⟩ y hy) Psi hPsi hPsic hRep chi hchi hchic hSupp
  have hFinite:=hCoercive lambda hlam hlamC' delta hd hd1 hBoot
  unfold NativeFinitePhysicalCoerciveBound at hFinite
  have hDensity:=HC lambda ⟨hlam.le,hlamG'.trans hGRoom⟩ delta Rstar c Dgraph p hc chi hchi hchic hSupp hRange
    Psi hPsi U5 hU5 hU5c hEq F f hf hfc hNorm hOutput hCore hFData hFinite
  exact hDensity.trans (le_max_left _ _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
