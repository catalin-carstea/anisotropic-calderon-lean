import Calderon.ActualOriginalLocalFrontierOnNativeCover
import Calderon.ActualOriginalPairFiniteCoercivity
import Calderon.ActualCenteredNativeCover
import Calderon.ActualPairLocalCarrierSourceImage
import Calderon.ActualNormalizedSmoothSourceKernelBundle
import Calderon.ActualSourcePartnerMetricRecovery
import Calderon.ActualRadiusTwoSourcePartnerSmoothness
import Calderon.ExteriorIdentityHomeomorphExtension
import Calderon.ActualRadiusTwoSourceSeparation
import Calderon.CollaboratorUnitBallValueTraceKernelOct17

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
def OriginalPairChosenCoverFinitePhysicalCoercivity
    (original1 original2:MatrixField) (tau0:UnitBallValueTrace):Prop :=
  ∀ S:KnownSideSourceData,S.original1=original1 → S.original2=original2 →
  ‖S.Xi1 0‖ ≤ 1 → ‖S.Xi2 0‖ ≤ 1 →
  (∀ x∈S.coordinateRoom,S.Xi1 x∉closure (fixedExteriorSourceOpens:Set R3) ∧
    S.Xi2 x∉closure (fixedExteriorSourceOpens:Set R3)) →
  (∀ s:𝓓(fixedExteriorSourceOpens,ℝ),∀ x∈S.W,
    radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x)=
    radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x)) →
  ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L → ∃ cover:NativeNormalCover S L,
  (∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho) ∧
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
def TwoSidedOriginalChosenCoverFinitePhysicalCoercivity (original1 original2:MatrixField):Prop :=
  ∃ tau0:UnitBallValueTrace,
    OriginalPairChosenCoverFinitePhysicalCoercivity original1 original2 tau0 ∧
    OriginalPairChosenCoverFinitePhysicalCoercivity original2 original1 tau0

/-- The earlier sufficient all-cover estimate implies this strictly less
prescriptive chosen-cover interface. Earlier checked consumers are preserved. -/
theorem original_pair_chosen_cover_finite_coercivity_of_all_cover_estimate
    (original1 original2:MatrixField) (tau0:UnitBallValueTrace)
    (h:OriginalPairFinitePhysicalCoercivity original1 original2 tau0):
    OriginalPairChosenCoverFinitePhysicalCoercivity original1 original2 tau0 := by
  intro S hOrig1 hOrig2 hFirst hSecond hFree hMatch
  obtain ⟨L0,hL0,HL⟩ := h S hOrig1 hOrig2 hFirst hSecond hFree hMatch
  refine ⟨L0,hL0,?_⟩
  intro L hL
  obtain ⟨cover,hCenter⟩ := NativeCenteredCover.exists_nativeNormalCover_with_rho_center_room S L
  exact ⟨cover,hCenter,HL L hL cover hCenter⟩

theorem twoSided_original_chosen_cover_finite_coercivity_of_all_cover_estimate
    (original1 original2:MatrixField) (h:TwoSidedOriginalFinitePhysicalCoercivity original1 original2):
    TwoSidedOriginalChosenCoverFinitePhysicalCoercivity original1 original2 := by
  obtain ⟨tau0,h12,h21⟩ := h
  exact ⟨tau0,original_pair_chosen_cover_finite_coercivity_of_all_cover_estimate original1 original2 tau0 h12,
    original_pair_chosen_cover_finite_coercivity_of_all_cover_estimate original2 original1 tau0 h21⟩

/-- Cofinal finite physical coercivity meets the already proved original
source-free continuation profile on exactly the same cover and cutoff. -/
theorem original_pair_local_metric_extension_of_chosen_cover_finite_physical_coercivity
    (original1 original2:MatrixField) (tau0:UnitBallValueTrace)
    (hKernel:UnitBallValueTraceKernel tau0)
    (hCoercive:OriginalPairChosenCoverFinitePhysicalCoercivity original1 original2 tau0):
    ActualSourceFreeLocalMetricExtensionFor original1 original2 := by
  intro S hOrig1 hOrig2 hFirst hSecond hFree hMatch
  have hCProfile:=hCoercive S hOrig1 hOrig2 hFirst hSecond hFree hMatch
  let LC:ℝ := Classical.choose hCProfile
  have hCData:=Classical.choose_spec hCProfile
  have hLC:0 < LC := hCData.1
  have HC:=hCData.2
  have hFProfile:=exists_original_local_frontier_of_finite_physical_coercivity_on_native_cover
    fixedSobolevCalculus fixedDirichletRegularity sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics tau0 hKernel S hFree hMatch 1 1 (by norm_num) (by norm_num)
  let LF:ℝ := Classical.choose hFProfile
  have hFData:=Classical.choose_spec hFProfile
  have HF:=hFData.2
  let L:ℝ := max LF LC
  have hLF:LF ≤ L := le_max_left _ _
  have hLC':LC ≤ L := le_max_right _ _
  have hCoverChoice:=HC L hLC'
  let cover:NativeNormalCover S L := Classical.choose hCoverChoice
  have hCoverData:=Classical.choose_spec hCoverChoice
  have hCenter:=hCoverData.1
  have hCPChoice:=hCoverData.2
  let pC:ℕ := Classical.choose hCPChoice
  have hCPData:=Classical.choose_spec hCPChoice
  have HCP:=hCPData.2
  have hFPChoice:=HF L hLF cover hCenter
  let pF:ℕ := Classical.choose hFPChoice
  have hFPData:=Classical.choose_spec hFPChoice
  have HFP:=hFPData.2
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

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature SphereHarmonic

/-- The original global source-evaluation images follow from the explicit
unproved two-sided cofinal finite physical estimate, via genuine strict
extensions of arbitrary admissible source-matched regions. -/
theorem original_sourceEvaluation_ranges_eq_of_chosen_cover_finite_physical_coercivity
    (g1 g2:MatrixField) (hg1:IsAdmissibleMetric g1) (hg2:IsAdmissibleMetric g2)
    (hEnergy:∀ f:R3→ℝ,ContDiff ℝ ∞ f → minimalEnergy g1 f=minimalEnergy g2 f)
    (hCoercive:TwoSidedOriginalChosenCoverFinitePhysicalCoercivity g1 g2):
    range (fun p:(radiusTwoOpens:Set R3)=>radiusTwoSourceEvaluationFamily
      fixedDirichletRegularity fixedSobolevCalculus g1 hg1 p)=
    range (fun p:(radiusTwoOpens:Set R3)=>radiusTwoSourceEvaluationFamily
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 p) := by
  obtain ⟨tau0,hFinite12,hFinite21⟩ := hCoercive
  have hKernel:UnitBallValueTraceKernel tau0 := unitBallValueTraceKernel tau0
  have hLocal12:=original_pair_local_metric_extension_of_chosen_cover_finite_physical_coercivity
    g1 g2 tau0 hKernel hFinite12
  have hLocal21:=original_pair_local_metric_extension_of_chosen_cover_finite_physical_coercivity
    g2 g1 tau0 hKernel hFinite21
  obtain ⟨K1,G1,K2,G2,hK1,hK2,_⟩ :=
    exists_twoMetric_normalizedSmoothInverseSourceKernels_exterior_eq
      fixedDirichletRegularity fixedSobolevCalculus g1 g2 hg1 hg2 hEnergy
  exact original_sourceEvaluation_ranges_eq_of_pair_local_carriers
    g1 g2 hg1 hg2 hEnergy radiusTwoSourceSeparation K1 K2 G1 G2 hK1 hK2 hLocal12 hLocal21

/-- Explicitly CONDITIONAL endpoint with the frozen Main conclusion. The
additional finite physical estimate is still unproved; this theorem does
not replace or discharge the frozen unconditional main. -/
theorem exists_isometryFixingExterior_of_chosen_cover_finite_physical_coercivity
    (g1 g2:MatrixField) (hg1:IsAdmissibleMetric g1) (hg2:IsAdmissibleMetric g2)
    (hEnergy:∀ f:R3→ℝ,ContDiff ℝ ∞ f → minimalEnergy g1 f=minimalEnergy g2 f)
    (hCoercive:TwoSidedOriginalChosenCoverFinitePhysicalCoercivity g1 g2):
    ∃ Phi:R3≃R3,IsIsometryFixingExterior Phi g1 g2 := by
  classical
  let hreg:FixedDirichletRegularity := fixedDirichletRegularity
  let hcalc:FixedSobolevCalculus := fixedSobolevCalculus
  let hSep:RadiusTwoSourceSeparation := radiusTwoSourceSeparation
  have hImage:=original_sourceEvaluation_ranges_eq_of_chosen_cover_finite_physical_coercivity
    g1 g2 hg1 hg2 hEnergy hCoercive
  let e : (radiusTwoOpens : Set R3) ≃ₜ (radiusTwoOpens : Set R3) :=
    radiusTwoSourcePartnerHomeomorph hreg hcalc hSep g2 g1 hg2 hg1 hImage.symm
  let F : R3 → R3 := fun x => if hx : x ∈ (radiusTwoOpens : Set R3) then
    (e ⟨x,hx⟩ : R3) else x
  let G : R3 → R3 := fun x => if hx : x ∈ (radiusTwoOpens : Set R3) then
    (e.symm ⟨x,hx⟩ : R3) else x
  have hF : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      F x = (e ⟨x,hx⟩ : R3) := by
    intro x hx
    simp only [F, dite_eq_left hx]
  have hG : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      G x = (e.symm ⟨x,hx⟩ : R3) := by
    intro x hx
    simp only [G, dite_eq_left hx]
  have hAnn : ∀ x : R3, ∀ hx : x ∈ (radiusTwoOpens : Set R3),
      1 < ‖x‖ → (e ⟨x,hx⟩ : R3) = x := by
    intro x hx hnorm
    have hxE : x ∈ (exteriorAnnulusOpens : Set R3) :=
      ⟨hnorm, mem_ball_zero_iff.mp hx⟩
    exact congrArg Subtype.val (radiusTwoSourcePartnerHomeomorph_eq_self_of_exterior
      hreg hcalc hSep g2 g1 hg2 hg1 hImage.symm
      (fun f hf => (hEnergy f hf).symm) ⟨x,hx⟩ hxE)
  have hSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ F x :=
    contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped
      hreg hcalc hSep g1 g2 hg1 hg2 hImage.symm F hF
  have hInvSmooth : ∀ x ∈ (radiusTwoOpens : Set R3), ContDiffAt ℝ ∞ G x :=
    contDiffAt_radiusTwoSourcePartnerHomeomorph_swapped_symm
      hreg hcalc hSep g1 g2 hg1 hg2 hImage.symm G hG
  let Phi : R3 ≃ R3 := radiusTwoIdentityExtensionEquiv e F G hF hG
  have hPhi : ContDiff ℝ ∞ (Phi : R3 → R3) :=
    contDiff_radiusTwoIdentityExtension e F hF hAnn hSmooth
  have hInv : ContDiff ℝ ∞ (Phi.symm : R3 → R3) :=
    contDiff_radiusTwoIdentityExtension e.symm G hG
      (radiusTwoHomeomorph_symm_fixes_annulus e hAnn) hInvSmooth
  have hFix : ∀ x : R3, 1 ≤ ‖x‖ → Phi x = x :=
    radiusTwoIdentityExtension_fixes_exterior e F hF hAnn hSmooth
  have hMatch : ∀ x ∈ (radiusTwoOpens : Set R3),
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g2 hg2 s x =
        radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus g1 hg1 s (Phi x) := by
    intro x hx s
    have hPhiAt : Phi x = (e ⟨x,hx⟩ : R3) :=
      (radiusTwoIdentityExtension_apply_of_mem F x hx).trans (hF x hx)
    rw [hPhiAt]
    exact (radiusTwoSourcePartnerHomeomorph_response hreg hcalc hSep
      g2 g1 hg2 hg1 hImage.symm ⟨x,hx⟩ s).symm
  exact ⟨Phi, hPhi, hInv, hFix,
    metric_eq_pullback_of_source_response_eq g1 g2 hg1 hg2 Phi hPhi hInv hFix hMatch⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
