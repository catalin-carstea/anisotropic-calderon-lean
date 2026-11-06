import Calderon.ActualMaximalSourceMatchedRegion
import Calderon.ActualFrontierAdmissibleSourceExtension
import Calderon.ActualSourceFreeKnownSideRestriction
import Calderon.ActualFrontierOriginalSourceData

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature MetricOperator MetricVolume
  ConnectionError

/-- The exact remaining local metric-extension input, restricted to genuine
source-free original carriers with all-source known-side agreement. -/
def ActualSourceFreeLocalMetricExtensionFor (original1 original2:MatrixField) : Prop :=
  ∀ S : KnownSideSourceData,
    S.original1 = original1 → S.original2 = original2 →
    ‖S.Xi1 0‖ ≤ 1 → ‖S.Xi2 0‖ ≤ 1 →
    (∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3)) →
    (∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
        S.original2_admissible s (S.Xi2 x)) →
    ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ S.coordinateRoom ∧
      EqOn S.g1 S.g2 (ball (0 : R3) r)

/-- A local exact transport of the match record across literal identities of
the source calculus and original metrics; all admissibility proofs are Props. -/
private theorem exists_pair_admissible_match_of_parameters_eq
    (reg1 reg2 : FixedDirichletRegularity) (calc1 calc2 : FixedSobolevCalculus)
    (g1 g2 k1 k2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hk1 : IsAdmissibleMetric k1) (hk2 : IsAdmissibleMetric k2)
    (hReg : reg1 = reg2) (hCalc : calc1 = calc2)
    (hG1 : g1 = k1) (hG2 : g2 = k2)
    (A : ActualAdmissibleSourceMatch reg1 calc1 g1 g2 hg1 hg2) :
    ∃ B : ActualAdmissibleSourceMatch reg2 calc2 k1 k2 hk1 hk2,
      B.domain = A.domain ∧ B.map = A.map := by
  cases hReg
  cases hCalc
  cases hG1
  cases hG2
  exact ⟨A,rfl,rfl⟩

/-- The actual original frontier selector, source-free restriction, local
metric extension and all-source UCP strictly enlarge any proper admissible
match, with no assumption that the match is merely the initial annulus. -/
theorem actual_admissible_strict_extension_of_pair_local_carrier
    (original1 original2 : MatrixField)
    (hOriginal1 : IsAdmissibleMetric original1)
    (hOriginal2 : IsAdmissibleMetric original2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f →
      minimalEnergy original1 f = minimalEnergy original2 f)
    (hSep : RadiusTwoSourceSeparation)
    (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hKernel1 : IsRadiusTwoSeparatelySmoothInverseSourceKernel
      original1 hOriginal1 K1 G1)
    (hKernel2 : IsRadiusTwoSeparatelySmoothInverseSourceKernel
      original2 hOriginal2 K2 G2)
    (hLocal : ActualSourceFreeLocalMetricExtensionFor original1 original2)
    (A : ActualAdmissibleSourceMatch fixedDirichletRegularity fixedSobolevCalculus
      original1 original2 hOriginal1 hOriginal2)
    (hMissing : ∃ x ∈ (radiusTwoOpens : Set R3), x ∉ A.domain) :
    ∃ C : ActualAdmissibleSourceMatch fixedDirichletRegularity fixedSobolevCalculus
        original1 original2 hOriginal1 hOriginal2,
      A.domain ⊆ C.domain ∧ ∃ p ∈ C.domain, p ∉ A.domain := by
  have hFix : ∀ x ∈ (fixedExteriorSourceOpens : Set R3), A.map x = x := by
    intro x hx
    exact A.exterior_fixed x (fixedExteriorSourceOpens_le_annulus hx)
  have hMatch : ∀ x ∈ A.domain,
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus
        original2 hOriginal2 x =
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus
        original1 hOriginal1 (A.map x) := by
    intro x hx
    exact (A.source_eq x hx).symm
  obtain ⟨center,p,q,S,hClosed,hBallW,hSphere,hpR,hpNorm,hNot,hClosure,
    hqR,hqNorm,hReg,hCalc,hOrig1,hOrig2,hK1,hK2,hG1,hG2,hXi1,hXi2,
    hNorm1,hNorm2,hMatchS⟩ :=
    exists_actual_original_source_data_at_missing_known_point original1 original2
      hOriginal1 hOriginal2 hEnergy K1 K2 G1 G2 hKernel1 hKernel2
      A.domain A.domain_open A.domain_connected A.domain_room A.exterior_subset
      A.map A.map_room A.map_smooth A.map_injective A.map_jacobian A.metric_eq
      hFix hMatch hMissing
  obtain ⟨T,hTReg,hTCalc,hTOrig1,hTOrig2,hTK1,hTK2,hTG1,hTG2,
    hTXi1,hTXi2,hTg1,hTg2,hTSep,hTRoom,hTW,hFree,hPreserve⟩ :=
    exists_known_side_source_data_with_source_free_room S hNorm1 hNorm2
  have hTNorm1 : ‖T.Xi1 0‖ ≤ 1 := by rw [hTXi1]; exact hNorm1
  have hTNorm2 : ‖T.Xi2 0‖ ≤ 1 := by rw [hTXi2]; exact hNorm2
  have hMatchT : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ T.W,
      radiusTwoSmoothSourceResponse T.hreg T.hcalc T.original1 T.original1_admissible s
        (T.Xi1 x) =
      radiusTwoSmoothSourceResponse T.hreg T.hcalc T.original2 T.original2_admissible s
        (T.Xi2 x) := by
    intro s
    exact hPreserve s (hMatchS s)
  obtain ⟨r,hr,hRoom,hMetric⟩ := hLocal T (hTOrig1.trans hOrig1) (hTOrig2.trans hOrig2) hTNorm1 hTNorm2 hFree hMatchT
  have hAll := original_source_responses_eqOn_ball_of_metric_eqOn
    T hFree hMatchT r hr hRoom hMetric
  have htReg : T.hreg = fixedDirichletRegularity := hTReg.trans hReg
  have htCalc : T.hcalc = fixedSobolevCalculus := hTCalc.trans hCalc
  have htOrig1 : T.original1 = original1 := hTOrig1.trans hOrig1
  have htOrig2 : T.original2 = original2 := hTOrig2.trans hOrig2
  obtain ⟨A',hA'domain,hA'map⟩ :=
    exists_pair_admissible_match_of_parameters_eq
      fixedDirichletRegularity T.hreg fixedSobolevCalculus T.hcalc
      original1 original2 T.original1 T.original2 hOriginal1 hOriginal2
      T.original1_admissible T.original2_admissible
      htReg.symm htCalc.symm htOrig1.symm htOrig2.symm A
  have hContact : T.Xi2 0 = p := by rw [hTXi2,hXi2]
  have hFrontier : T.Xi2 0 ∈ closure A'.domain := by
    rw [hContact,hA'domain]
    exact hClosure
  obtain ⟨C',hC'domain,hC'contact,hC'old⟩ :=
    exists_admissible_source_match_at_contact_frontier T hSep A' r hr hRoom
      hMetric hAll hFrontier
  obtain ⟨C,hCdomain,hCmap⟩ :=
    exists_pair_admissible_match_of_parameters_eq
      T.hreg fixedDirichletRegularity T.hcalc fixedSobolevCalculus
      T.original1 T.original2 original1 original2 T.original1_admissible
      T.original2_admissible hOriginal1 hOriginal2
      htReg htCalc htOrig1 htOrig2 C'
  refine ⟨C,?_,p,?_,hNot⟩
  · rw [hCdomain,hC'domain,hA'domain]
    exact subset_union_left
  · rw [hCdomain,← hContact]
    exact hC'contact

/-- The genuine two-sided local carrier theorem yields equality of the
literal original source-evaluation images through actual maximal matches. -/
theorem original_sourceEvaluation_ranges_eq_of_pair_local_carriers
    (original1 original2 : MatrixField)
    (hOriginal1 : IsAdmissibleMetric original1)
    (hOriginal2 : IsAdmissibleMetric original2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f →
      minimalEnergy original1 f = minimalEnergy original2 f)
    (hSep : RadiusTwoSourceSeparation)
    (K1 K2 : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G1 G2 : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hKernel1 : IsRadiusTwoSeparatelySmoothInverseSourceKernel
      original1 hOriginal1 K1 G1)
    (hKernel2 : IsRadiusTwoSeparatelySmoothInverseSourceKernel
      original2 hOriginal2 K2 G2)
    (hLocal12 : ActualSourceFreeLocalMetricExtensionFor original1 original2)
    (hLocal21 : ActualSourceFreeLocalMetricExtensionFor original2 original1) :
    range (fun p : (radiusTwoOpens : Set R3) =>
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus
        original1 hOriginal1 p) =
    range (fun p : (radiusTwoOpens : Set R3) =>
      radiusTwoSourceEvaluationFamily fixedDirichletRegularity fixedSobolevCalculus
        original2 hOriginal2 p) := by
  apply sourceEvaluation_ranges_eq_of_actual_admissible_extensions
    fixedDirichletRegularity fixedSobolevCalculus hSep original1 original2
      hOriginal1 hOriginal2 hEnergy
  · intro A hMissing
    exact actual_admissible_strict_extension_of_pair_local_carrier original1 original2
      hOriginal1 hOriginal2 hEnergy hSep K1 K2 G1 G2 hKernel1 hKernel2 hLocal12 A hMissing
  · intro A hMissing
    exact actual_admissible_strict_extension_of_pair_local_carrier original2 original1
      hOriginal2 hOriginal1 (fun f hf => (hEnergy f hf).symm) hSep
      K2 K1 G2 G1 hKernel2 hKernel1 hLocal21 A hMissing

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
