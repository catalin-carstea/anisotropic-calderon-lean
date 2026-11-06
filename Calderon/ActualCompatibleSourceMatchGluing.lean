import Calderon.ActualSourceMatchedRegion

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily Literature ConnectionError NativeSourceChartCalculus
open MetricOperator NormalCoordinatesFrame MetricVolume

/-- Glue an admissible original-source match to an overlapping local
original-source match. The glued map retains both exact restrictions. -/
theorem exists_admissible_source_match_union_local
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (hSep : RadiusTwoSourceSeparation)
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1)
    (hg2 : IsAdmissibleMetric g2)
    (A : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2)
    (B : ActualLocalSourceMatchedRegion hreg hcalc g1 g2 hg1 hg2)
    (hOverlap : (A.domain ∩ B.domain).Nonempty) :
    ∃ C : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2,
      C.domain = A.domain ∪ B.domain ∧
      EqOn C.map A.map A.domain ∧
      EqOn C.map B.map B.domain := by
  classical
  let U : Set R3 := A.domain ∪ B.domain
  let Phi : R3 → R3 := fun x => if x ∈ A.domain then A.map x else B.map x
  have hOnA : EqOn Phi A.map A.domain := by
    intro x hx
    simp [Phi, hx]
  have hOnB : EqOn Phi B.map B.domain := by
    intro x hx
    by_cases ha : x ∈ A.domain
    · simpa [Phi, ha] using
        actualLocalSourceMatchedRegion_maps_eq_on_overlap hreg hcalc hSep g1 g2
          hg1 hg2 A.toActualLocalSourceMatchedRegion B x ha hx
    · simp [Phi, ha]
  have hGermA (x : R3) (hx : x ∈ A.domain) : Phi =ᶠ[𝓝 x] A.map := by
    filter_upwards [A.domain_open.mem_nhds hx] with y hy
    exact hOnA hy
  have hGermB (x : R3) (hx : x ∈ B.domain) : Phi =ᶠ[𝓝 x] B.map := by
    filter_upwards [B.domain_open.mem_nhds hx] with y hy
    exact hOnB hy
  have hUopen : IsOpen U := A.domain_open.union B.domain_open
  have hUconn : IsConnected U := by
    exact A.domain_connected.union hOverlap B.domain_connected
  have hRoom : U ⊆ (radiusTwoOpens : Set R3) := by
    intro x hx
    rcases hx with hx | hx
    · exact A.domain_room hx
    · exact B.domain_room hx
  have hMapRoom : ∀ x ∈ U, Phi x ∈ (radiusTwoOpens : Set R3) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hOnA hx]; exact A.map_room x hx
    · rw [hOnB hx]; exact B.map_room x hx
  have hSmooth : ContDiffOn ℝ ∞ Phi U := by
    intro x hx
    rcases hx with hx | hx
    · exact ((A.map_smooth.contDiffAt (A.domain_open.mem_nhds hx)).congr_of_eventuallyEq
        (hGermA x hx)).contDiffWithinAt
    · exact ((B.map_smooth.contDiffAt (B.domain_open.mem_nhds hx)).congr_of_eventuallyEq
        (hGermB x hx)).contDiffWithinAt
  have hSource : ∀ x ∈ U,
      radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (Phi x) =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hOnA hx]; exact A.source_eq x hx
    · rw [hOnB hx]; exact B.source_eq x hx
  have hInj : InjOn Phi U := by
    intro x hx y hy hxy
    have hFamily : radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 x =
        radiusTwoSourceEvaluationFamily hreg hcalc g2 hg2 y := by
      calc
        _ = radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (Phi x) := (hSource x hx).symm
        _ = radiusTwoSourceEvaluationFamily hreg hcalc g1 hg1 (Phi y) := by rw [hxy]
        _ = _ := hSource y hy
    have h := radiusTwoSourceEvaluationFamily_injective hreg hcalc hSep g2 hg2
      (a₁ := ⟨x,hRoom hx⟩) (a₂ := ⟨y,hRoom hy⟩) hFamily
    exact congrArg Subtype.val h
  have hJac : ∀ x ∈ U, IsUnit (coordinateJacobianMatrix Phi x).det := by
    intro x hx
    rcases hx with hx | hx
    · rw [coordinateJacobianMatrix_eq_of_eventuallyEq Phi A.map x (hGermA x hx)]
      exact A.map_jacobian x hx
    · rw [coordinateJacobianMatrix_eq_of_eventuallyEq Phi B.map x (hGermB x hx)]
      exact B.map_jacobian x hx
  have hMetric : EqOn (pullbackMetric g1 Phi) g2 U := by
    intro x hx
    rcases hx with hx | hx
    · rw [pullbackMetric_eq_of_eventuallyEq g1 Phi A.map x (hGermA x hx)]
      exact A.metric_eq hx
    · rw [pullbackMetric_eq_of_eventuallyEq g1 Phi B.map x (hGermB x hx)]
      exact B.metric_eq hx
  let C : ActualAdmissibleSourceMatch hreg hcalc g1 g2 hg1 hg2 := {
    toActualLocalSourceMatchedRegion := {
      domain := U
      domain_open := hUopen
      domain_connected := hUconn
      domain_room := hRoom
      map := Phi
      map_room := hMapRoom
      map_smooth := hSmooth
      map_injective := hInj
      map_jacobian := hJac
      metric_eq := hMetric
      source_eq := hSource }
    exterior_subset := fun x hx => Or.inl (A.exterior_subset hx)
    exterior_fixed := by
      intro x hx
      rw [hOnA (A.exterior_subset hx)]
      exact A.exterior_fixed x hx }
  exact ⟨C, rfl, hOnA, hOnB⟩

end OAI.AnisotropicCalderon.ExteriorSource
