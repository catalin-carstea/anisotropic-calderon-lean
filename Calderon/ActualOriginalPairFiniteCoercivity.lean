import Calderon.ActualOriginalFiniteCoercivityLocalFrontier
import Calderon.ActualPairLocalCarrierSourceImage
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature SphereHarmonic ConformalDepth
  DirichletFamily.DriftBootstrap
attribute [local irreducible] NativeFinitePhysicalCoerciveBound

/-- A sufficient cofinal finite physical estimate, restricted to source-matched
carriers of the literal ordered original metric pair. It is an unproved
conditional input, not a literature adoption. Constants may depend on the
carrier, cover, ordered geometric parameters, and the eventual cutoff, but
are fixed before the final dilation and shrinking radius. -/
def OriginalPairFinitePhysicalCoercivity
    (original1 original2:MatrixField) (tau0:UnitBallValueTrace):Prop :=
  ∀ S:KnownSideSourceData,S.original1=original1 → S.original2=original2 →
  ‖S.Xi1 0‖ ≤ 1 → ‖S.Xi2 0‖ ≤ 1 →
  (∀ x∈S.coordinateRoom,S.Xi1 x∉closure (fixedExteriorSourceOpens:Set R3) ∧
    S.Xi2 x∉closure (fixedExteriorSourceOpens:Set R3)) →
  (∀ s:𝓓(fixedExteriorSourceOpens,ℝ),∀ x∈S.W,
    radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x)=
    radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x)) →
  ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L → ∀ cover:NativeNormalCover S L,
  (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) →
  ∃ p0:ℕ,2 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
  ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
  ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 →
  ∀ tb:ℝ,0 < tb → ∀ chi:R3→ℝ,ContDiff ℝ ∞ chi →
  range chi⊆Icc (0:ℝ) 1 → tsupport chi⊆interior cylinder →
  tsupport (fderiv ℝ chi)⊆{y:R3 | y 2 < -(1/4:ℝ)}∪{y:R3 | tb < referenceDepth L y} →
  ∃ c lambdaC:ℝ,0 < c ∧ 0 < lambdaC ∧
  ∀ lambda:ℝ,0 < lambda → lambda ≤ lambdaC → ∀ delta:ℝ,0 < delta → delta ≤ 1 →
    CurrentRadiusBootstrap S L lambda delta Rstar eps p →
    NativeFinitePhysicalCoerciveBound fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics tau0 S L cover chi lambda delta Rstar p c

/-- This named hypothesis retains both directional estimates; no symmetry of
the physical operator or of its coercivity proof is assumed. -/
def TwoSidedOriginalFinitePhysicalCoercivity (original1 original2:MatrixField):Prop :=
  ∃ tau0:UnitBallValueTrace,
    OriginalPairFinitePhysicalCoercivity original1 original2 tau0 ∧
    OriginalPairFinitePhysicalCoercivity original2 original1 tau0

/-- Cofinal finite physical coercivity meets the already proved original
source-free continuation profile on exactly the same cover and cutoff. -/
theorem original_pair_local_metric_extension_of_finite_physical_coercivity
    (original1 original2:MatrixField) (tau0:UnitBallValueTrace)
    (hKernel:UnitBallValueTraceKernel tau0)
    (hCoercive:OriginalPairFinitePhysicalCoercivity original1 original2 tau0):
    ActualSourceFreeLocalMetricExtensionFor original1 original2 := by
  intro S hOrig1 hOrig2 hFirst hSecond hFree hMatch
  have hCProfile:=hCoercive S hOrig1 hOrig2 hFirst hSecond hFree hMatch
  let LC:ℝ := Classical.choose hCProfile
  have hCData:=Classical.choose_spec hCProfile
  have hLC:0 < LC := hCData.1
  have HC:=hCData.2
  have hFProfile:=exists_original_local_frontier_of_finite_physical_coercivity
    fixedSobolevCalculus fixedDirichletRegularity sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics tau0 hKernel S hFree hMatch 1 1 (by norm_num) (by norm_num)
  let LF:ℝ := Classical.choose hFProfile
  have hFData:=Classical.choose_spec hFProfile
  have HF:=hFData.2
  let L:ℝ := max LF LC
  have hLF:LF ≤ L := le_max_left _ _
  have hLC':LC ≤ L := le_max_right _ _
  have hCoverChoice:=HF L hLF
  let cover:NativeNormalCover S L := Classical.choose hCoverChoice
  have hCoverData:=Classical.choose_spec hCoverChoice
  have hCenter:=hCoverData.1
  have hFPChoice:=hCoverData.2
  let pF:ℕ := Classical.choose hFPChoice
  have hFPData:=Classical.choose_spec hFPChoice
  have HFP:=hFPData.2
  have hCPChoice:=HC L hLC' cover hCenter
  let pC:ℕ := Classical.choose hCPChoice
  have hCPData:=Classical.choose_spec hCPChoice
  have HCP:=hCPData.2
  let p:ℕ := max pF pC
  have hpF:pF ≤ p := le_max_left _ _
  have hpC:pC ≤ p := le_max_right _ _
  have hFEChoice:=HFP p hpF
  let epsF:ℝ := Classical.choose hFEChoice
  have hFEData:=Classical.choose_spec hFEChoice
  have hepsF:0 < epsF := hFEData.1
  have HFE:=hFEData.2.2
  have hCEChoice:=HCP p hpC
  let epsC:ℝ := Classical.choose hCEChoice
  have hCEData:=Classical.choose_spec hCEChoice
  have hepsC:0 < epsC := hCEData.1
  have HCE:=hCEData.2.2
  let eps:ℝ := min epsF epsC
  have heps:0 < eps := lt_min hepsF hepsC
  have hepsF':eps ≤ epsF := min_le_left _ _
  have hepsC':eps ≤ epsC := min_le_right _ _
  have hFRChoice:=HFE eps heps hepsF'
  let RF:ℝ := Classical.choose hFRChoice
  have hFRData:=Classical.choose_spec hFRChoice
  have hRF:0 < RF := hFRData.1
  have HFR:=hFRData.2
  have hCRChoice:=HCE eps heps hepsC'
  let RC:ℝ := Classical.choose hCRChoice
  have hCRData:=Classical.choose_spec hCRChoice
  have hRC:0 < RC := hCRData.1
  have HCR:=hCRData.2
  let Rstar:ℝ := min RF RC
  have hRs:0 < Rstar := lt_min hRF hRC
  have hRsF:Rstar ≤ RF := min_le_left _ _
  have hRsC:Rstar ≤ RC := min_le_right _ _
  obtain ⟨eta,tb,hEta,hEtaCover,htb,hthree,hKcompact,hKinside,
    chi,hchi,hchic,hRange,hSupp,W,hWopen,hKW,hWOne,hDeriv,HFrontier⟩ :=
    HFR Rstar hRs hRsF
  have hFiniteChoice:=HCR Rstar hRs hRsC tb htb chi hchi hRange hSupp hDeriv
  let c:ℝ := Classical.choose hFiniteChoice
  have hLambdaChoice:=Classical.choose_spec hFiniteChoice
  let lambdaC:ℝ := Classical.choose hLambdaChoice
  have hFiniteData:=Classical.choose_spec hLambdaChoice
  have hc:0 < c := hFiniteData.1
  have hlamC:0 < lambdaC := hFiniteData.2.1
  have hFinite:=hFiniteData.2.2
  have hFrontierChoice:=HFrontier c lambdaC hc hlamC hFinite
  let lambda:ℝ := Classical.choose hFrontierChoice
  have hFrontierData:=Classical.choose_spec hFrontierChoice
  have hOutcome:ActualLocalFrontierOutcome S L lambda Rstar eps p := hFrontierData.2.2.2
  have hBallChoice:=hOutcome.contact_ball
  let r:ℝ := Classical.choose hBallChoice
  have hBallData:=Classical.choose_spec hBallChoice
  exact ⟨r,hBallData.1,hBallData.2.1,hBallData.2.2.1⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
