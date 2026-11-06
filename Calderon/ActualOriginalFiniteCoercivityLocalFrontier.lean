import Calderon.ActualCutoffDensityNormDictionary
import Calderon.ActualOrderedDensityCoercivityProfile
import Calderon.ActualSourceFreeFactoryLocalFrontier

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift CoordinateBootstrapJets
  ExteriorSource.MetricCompatibleSourceJetAlgebra RadiusProfile WeightedBaseSpectral
attribute [local irreducible] nativeDensitySphereL2L referenceBaseLift RepresentsNativeMixedKernelDensity

/-- The original source-free five-source continuation is reduced to the genuine
uniform finite physical coercivity inequality on its SAME cover and cutoff.
No positive coercivity constant is supplied by this theorem. -/
theorem exists_original_local_frontier_of_finite_physical_coercivity
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData)
    (hFree:∀ x∈S.coordinateRoom,
      S.Xi1 x∉closure (fixedExteriorSourceOpens:Set R3) ∧
      S.Xi2 x∉closure (fixedExteriorSourceOpens:Set R3))
    (hMatch:∀ s:𝓓(fixedExteriorSourceOpens,ℝ),∀ x∈S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x)=
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x))
    (bound separation:ℝ) (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∃ cover:NativeNormalCover S L,
      (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) ∧
      ∃ p0:ℕ,24 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
      ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
      ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 →
      ∃ eta tb:ℝ,0 < eta ∧ eta ≤ cover.dilationCeiling ∧
        0 < tb ∧ 3*tb < depthPrimitive L (1/8) (1/4) ∧
      let K:Set R3 := {y | y∈cylinder ∧ -(1/2:ℝ) ≤ y 2 ∧ referenceDepth L y ≤ 2*tb}
      IsCompact K ∧ K⊆interior cylinder ∧
      ∃ chi:R3→ℝ,ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        range chi⊆Icc (0:ℝ) 1 ∧ tsupport chi⊆interior cylinder ∧
      ∃ W:Set R3,IsOpen W ∧ K⊆W ∧ (∀ z∈W,chi z=1) ∧
        tsupport (fderiv ℝ chi)⊆{z:R3 | z 2 < -(1/4:ℝ)}∪{z:R3 | tb < referenceDepth L z} ∧
      ∀ (c lambdaC:ℝ),0 < c → 0 < lambdaC →
      (∀ lambda:ℝ,0 < lambda → lambda ≤ lambdaC → ∀ delta:ℝ,0 < delta → delta ≤ 1 →
        CurrentRadiusBootstrap S L lambda delta Rstar eps p →
        NativeFinitePhysicalCoerciveBound hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p c) →
      ∃ lambda:ℝ,0 < lambda ∧ lambda ≤ eta ∧ lambda ≤ lambdaC ∧
        ActualLocalFrontierOutcome S L lambda Rstar eps p := by
  obtain ⟨L0,hL0,H0⟩ := exists_original_ordered_density_coercivity_profile
    hcalc hreg hF hO hD tau0 hKernel S bound separation hBound hSep
  refine Exists.intro L0 ?_
  refine And.intro hL0 ?_
  intro L hL
  have hLpos:0 < L := hL0.trans_le hL
  obtain ⟨cover,hCenter,HP⟩ := H0 L hL
  refine Exists.intro cover ?_
  refine And.intro hCenter ?_
  let p0:ℕ := Classical.choose HP
  have hPData:=Classical.choose_spec HP
  have hp0:24 ≤ p0 := hPData.1
  have HPE:=hPData.2
  refine Exists.intro p0 ?_
  refine And.intro hp0 ?_
  intro p hp
  have hp24:24 ≤ p := hp0.trans hp
  have hEChoice:=HPE p hp
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
  intro Rstar hRs hRs0
  have hKernelChoice:=HR Rstar hRs hRs0
  let etaKernel:ℝ := Classical.choose hKernelChoice
  have hKernelData:=Classical.choose_spec hKernelChoice
  have hEtaKernel:0 < etaKernel := hKernelData.1
  have hBeta:=hKernelData.2.2.1
  have hRadius:=hKernelData.2.2.2.1
  have hKK:=hKernelData.2.2.2.2.1
  have HDensity:=hKernelData.2.2.2.2.2
  obtain ⟨eta,tb,hEta,hEtaCover,htb,hthree,hKcompact,hKinside,
    chi,hchi,hchic,hRange,hSupp,W,hWopen,hKW,hWOne,hDeriv,hContinuation⟩ :=
    exists_actual_factory_one_dilation_local_frontier_of_referenceBaseLift_bound_with_small_dilation_cap_of_source_free_room
      hcalc hreg hF hO hD tau0 hKernel S hFree hMatch L Rstar eps cover p
      bound separation etaKernel hLpos hRs heps hp24 hEtaKernel hBeta hRadius hKK
  refine Exists.intro eta ?_
  refine Exists.intro tb ?_
  refine And.intro hEta ?_
  refine And.intro hEtaCover ?_
  refine And.intro htb ?_
  refine And.intro hthree ?_
  refine And.intro hKcompact ?_
  refine And.intro hKinside ?_
  refine Exists.intro chi ?_
  refine And.intro hchi ?_
  refine And.intro hchic ?_
  refine And.intro hRange ?_
  refine And.intro hSupp ?_
  refine Exists.intro W ?_
  refine And.intro hWopen ?_
  refine And.intro hKW ?_
  refine And.intro hWOne ?_
  refine And.intro hDeriv ?_
  intro c lambdaC hc hlamC hCoercive
  have hDensityChoice:=HDensity tb htb chi hchi hRange hSupp hDeriv c lambdaC hc hlamC hCoercive
  let lambdaD:ℝ := Classical.choose hDensityChoice
  have hDChoice:=Classical.choose_spec hDensityChoice
  let D:ℝ := Classical.choose hDChoice
  have hDensityData:=Classical.choose_spec hDChoice
  have hlamD:0 < lambdaD := hDensityData.1
  have hDLower:1 ≤ D := hDensityData.2.2.1
  have HD:=hDensityData.2.2.2
  let etaD:ℝ := min lambdaD lambdaC
  have hEtaD:0 < etaD := lt_min hlamD hlamC
  obtain ⟨rho0,Cstar,hrho0,hCstar,HContinue⟩ :=
    hContinuation etaD hEtaD D (by linarith only [hDLower])
  have hLift:∀ lambda delta:ℝ,
      ∀ KK:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover,
      ∀ Psi:R3→SphereSobolev (3/2:ℝ),
      0 < lambda → lambda ≤ min eta etaD → 0 < delta → delta ≤ 1 →
      CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      ContDiff ℝ ∞ Psi → HasCompactSupport Psi →
      (∀ i:Fin cover.count,∀ y∈cylinder∩(cover.packet i).centers,∀ u:SmoothData,
        (∀ z∈(ballOpens:Set R3),coordinateFluxDivergence
          (metricDivergenceFlux (fun x=>S.g1 (lambda • x)) u.1)
          (packetEndpoint S L (cover.packet i) lambda y (referenceRadius delta Rstar p L y) z)=0) →
        nativeMixedKernelDensityFunctional hO hD tau0 S L (cover.packet i) lambda delta Rstar p Psi u y=
        nativeMixedKernelWronskianFlux S L (cover.packet i) lambda KK.kernel u.1 y
          (referenceRadius delta Rstar p L y) y) →
      let V:R3→SphereL2 := fun z=>chi z • (sphereSobolevZeroEquiv hO hD).symm
        (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (Psi z))
      ∀ hV:Continuous V,∀ hVc:HasCompactSupport V,
        ‖referenceBaseLift S.g1 S.g1_admissible L lambda V hV hVc‖ₑ ≤ ENNReal.ofReal D := by
    intro lambda delta KK Psi hlam hlamEta hd hd1 hBoot hPsi hPsic hIdentity V hV hVc
    have hlamD':lambda ≤ lambdaD :=
      (hlamEta.trans (min_le_right _ _)).trans (min_le_left _ _)
    have hRep:RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover KK Psi := by
      unfold RepresentsNativeMixedKernelDensity
      exact hIdentity
    have hNorm:=(HD lambda hlam hlamD' delta hd hd1 hBoot).2.2 KK Psi hPsi hPsic hRep
    exact referenceBaseLift_original_cutoff_density_enorm_le_of_norm_le
      S.g1 S.g1_admissible L lambda D hO hD chi hchi hchic Psi hPsi hNorm hV hVc
  obtain ⟨rho,lambda,hrho,hrho0',hlam,hlamEta,hFrontier⟩ := HContinue hLift
  exact ⟨lambda,hlam,hlamEta.trans (min_le_left _ _),
    (hlamEta.trans (min_le_right _ _)).trans (min_le_right _ _),hFrontier⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
