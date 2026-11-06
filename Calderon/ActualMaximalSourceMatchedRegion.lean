import Calderon.ActualSourceMatchedRegion
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature ConnectionError NativeSourceChartCalculus
open MetricOperator NormalCoordinatesFrame MetricVolume

/-- The union of ALL actual admissible matches is itself an admissible match.
Its map is well-defined by source separation, without a maximality premise. -/
theorem exists_maximal_actual_admissible_source_match
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g1 f = minimalEnergy g2 f) :
    ∃ A : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2,
      ∀ B : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2, B.domain ⊆ A.domain := by
  classical
  let M := ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2
  let m0 : M := initialActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2 hEnergy
  let W : Set R3 := ⋃ m : M, m.domain
  let Phi : R3 → R3 := fun x => if hx : x ∈ W then
    (Classical.choose (mem_iUnion.mp hx) : M).map x else x
  have hPhiEq (m : M) (x : R3) (hx : x ∈ m.domain) : Phi x = m.map x := by
    have hW : x ∈ W := mem_iUnion.mpr ⟨m,hx⟩
    have hChosen : x ∈ (Classical.choose (mem_iUnion.mp hW) : M).domain :=
      Classical.choose_spec (mem_iUnion.mp hW)
    have hh := actualLocalSourceMatchedRegion_maps_eq_on_overlap hreg hcalc hSep g1 g2 hg1 hg2
      (Classical.choose (mem_iUnion.mp hW) : M).toActualLocalSourceMatchedRegion
      m.toActualLocalSourceMatchedRegion x hChosen hx
    simpa only [Phi,dite_eq_left hW] using hh
  have hGerm (m : M) (x : R3) (hx : x ∈ m.domain) : Phi =ᶠ[nhds x] m.map := by
    filter_upwards [m.domain_open.mem_nhds hx] with y hy
    exact hPhiEq m y hy
  have hRoom : W ⊆ (radiusTwoOpens : Set R3) := by
    intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    exact m.domain_room hm
  have hMapRoom : ∀ x ∈ W, Phi x ∈ (radiusTwoOpens : Set R3) := by
    intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    rw [hPhiEq m x hm]
    exact m.map_room x hm
  have hSources : ∀ x ∈ W,
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (Phi x) =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 x := by
    intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    rw [hPhiEq m x hm]
    exact m.source_eq x hm
  have hInjective : InjOn Phi W := by
    intro x hx y hy hxy
    have hfam : radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 x =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 y :=
      (hSources x hx).symm.trans ((congrArg
        (radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1) hxy).trans (hSources y hy))
    have hh := radiusTwoSourceEvaluationFamily_injective hreg hcalc hSep g2 hg2
      (a₁ := ⟨x,hRoom hx⟩) (a₂ := ⟨y,hRoom hy⟩) hfam
    exact congrArg Subtype.val hh
  have hSmooth : ContDiffOn ℝ ∞ Phi W := by
    intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    exact ((m.map_smooth.contDiffAt (m.domain_open.mem_nhds hm)).congr_of_eventuallyEq
      (hGerm m x hm)).contDiffWithinAt
  have hJac : ∀ x ∈ W, IsUnit (coordinateJacobianMatrix Phi x).det := by
    intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    rw [coordinateJacobianMatrix_eq_of_eventuallyEq Phi m.map x (hGerm m x hm)]
    exact m.map_jacobian x hm
  have hMetric : EqOn (pullbackMetric g1 Phi) g2 W := by
    intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    rw [pullbackMetric_eq_of_eventuallyEq g1 Phi m.map x (hGerm m x hm)]
    exact m.metric_eq hm
  obtain ⟨e,he⟩ := MixedKernelConstructionTask.isConnected_exteriorAnnulusOpens.nonempty
  have hNonempty : W.Nonempty := ⟨e,mem_iUnion.mpr ⟨m0,m0.exterior_subset he⟩⟩
  have hPre : IsPreconnected W :=
    isPreconnected_iUnion ⟨e,mem_iInter.mpr (fun m : M => m.exterior_subset he)⟩
      (fun m => m.domain_connected.isPreconnected)
  let A : M := {
    toActualLocalSourceMatchedRegion := {
      domain := W
      domain_open := isOpen_iUnion (fun m : M => m.domain_open)
      domain_connected := ⟨hNonempty,hPre⟩
      domain_room := hRoom
      map := Phi
      map_room := hMapRoom
      map_smooth := hSmooth
      map_injective := hInjective
      map_jacobian := hJac
      metric_eq := hMetric
      source_eq := hSources }
    exterior_subset := fun x hx => mem_iUnion.mpr ⟨m0,m0.exterior_subset hx⟩
    exterior_fixed := fun x hx => (hPhiEq m0 x (m0.exterior_subset hx)).trans
      (m0.exterior_fixed x hx) }
  refine ⟨A,?_⟩
  intro B x hx
  exact mem_iUnion.mpr ⟨B,hx⟩

/-- A genuine local-extension criterion forces the maximal match to have
full domain. The criterion is an explicit project input, not a new axiom. -/
theorem exists_full_actual_admissible_source_match_of_extension
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g1 f = minimalEnergy g2 f)
    (hExtend : ∀ A : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2,
      (∃ x ∈ (radiusTwoOpens : Set R3), x ∉ A.domain) →
        ∃ B : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2,
          A.domain ⊆ B.domain ∧ ∃ x ∈ B.domain, x ∉ A.domain) :
    ∃ A : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2,
      A.domain = (radiusTwoOpens : Set R3) := by
  classical
  obtain ⟨A,hMax⟩ := exists_maximal_actual_admissible_source_match hreg hcalc hSep g1 g2 hg1 hg2 hEnergy
  by_cases hFull : (radiusTwoOpens : Set R3) ⊆ A.domain
  · exact ⟨A,Subset.antisymm A.domain_room hFull⟩
  · have hMissing : ∃ x ∈ (radiusTwoOpens : Set R3), x ∉ A.domain := by
      by_contra hNo
      apply hFull
      intro x hx
      by_contra hxA
      exact hNo ⟨x,hx,hxA⟩
    obtain ⟨B,hAB,x,hxB,hxA⟩ := hExtend A hMissing
    exact False.elim (hxA (hMax B hxB))

/-- A full actual admissible match gives inclusion of the literal source images. -/
theorem sourceEvaluation_range_subset_of_full_actual_admissible_source_match
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (A : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2)
    (hFull : A.domain = (radiusTwoOpens : Set R3)) :
    range (fun p : (radiusTwoOpens : Set R3) => radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 p) ⊆
      range (fun p : (radiusTwoOpens : Set R3) => radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 p) := by
  rintro v ⟨p,rfl⟩
  have hp : (p : R3) ∈ A.domain := hFull.symm ▸ p.property
  exact ⟨⟨A.map p,A.map_room p hp⟩,A.source_eq p hp⟩

/-- Symmetric actual local-extension criteria imply equality of the two
original source images; no image-equality premise or axiom is inserted. -/
theorem sourceEvaluation_ranges_eq_of_actual_admissible_extensions
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (hEnergy : ∀ f : R3 → ℝ, ContDiff ℝ ∞ f → minimalEnergy g1 f = minimalEnergy g2 f)
    (hForward : ∀ A : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2,
      (∃ x ∈ (radiusTwoOpens : Set R3), x ∉ A.domain) →
        ∃ B : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2,
          A.domain ⊆ B.domain ∧ ∃ x ∈ B.domain, x ∉ A.domain)
    (hBackward : ∀ A : ActualAdmissibleSourceMatch hreg hcalc g2 g1 hg2 hg1,
      (∃ x ∈ (radiusTwoOpens : Set R3), x ∉ A.domain) →
        ∃ B : ActualAdmissibleSourceMatch hreg hcalc g2 g1 hg2 hg1,
          A.domain ⊆ B.domain ∧ ∃ x ∈ B.domain, x ∉ A.domain) :
    range (fun p : (radiusTwoOpens : Set R3) => radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 p) =
      range (fun p : (radiusTwoOpens : Set R3) => radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 p) := by
  obtain ⟨A,hA⟩ := exists_full_actual_admissible_source_match_of_extension
    hreg hcalc hSep g1 g2 hg1 hg2 hEnergy hForward
  obtain ⟨B,hB⟩ := exists_full_actual_admissible_source_match_of_extension
    hreg hcalc hSep g2 g1 hg2 hg1 (fun f hf => (hEnergy f hf).symm) hBackward
  exact Subset.antisymm
    (sourceEvaluation_range_subset_of_full_actual_admissible_source_match hreg hcalc g2 g1 hg2 hg1 B hB)
    (sourceEvaluation_range_subset_of_full_actual_admissible_source_match hreg hcalc g1 g2 hg1 hg2 A hA)

end OAI.AnisotropicCalderon.ExteriorSource
