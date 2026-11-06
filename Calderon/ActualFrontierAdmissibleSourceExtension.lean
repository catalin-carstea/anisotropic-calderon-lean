import Calderon.ActualFrontierLocalPhysicalChart
import Calderon.ActualCompatibleSourceMatchGluing

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource MetricOperator MetricVolume ConnectionError Literature

/-- The exact local physical chart is an actual source-matched region for the
same original metric pair and the same exterior source-evaluation families. -/
theorem exists_actual_local_source_match_of_ball_all_source_agreement
    (S : KnownSideSourceData) (r : ℝ) (hr : 0 < r)
    (hRoom : ball (0 : R3) r ⊆ S.coordinateRoom)
    (hMetric : EqOn S.g1 S.g2 (ball (0 : R3) r))
    (hAll : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      EqOn (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (S.Xi1 z))
        (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
          S.original2_admissible s (S.Xi2 z)) (ball (0 : R3) r)) :
    ∃ B : ActualLocalSourceMatchedRegion S.hreg S.hcalc S.original1 S.original2
        S.original1_admissible S.original2_admissible,
      B.domain = S.Xi2 '' ball (0 : R3) r ∧ S.Xi2 0 ∈ B.domain := by
  obtain ⟨Z,Phi,hZ,hOpen,hConn,hContact,hRoomZ,hSmooth,hInj,hMapRoom,hJac,hPull,
      hSources,hChart⟩ :=
    exists_local_physical_match_of_ball_all_source_agreement S r hr hRoom hMetric hAll
  let B : ActualLocalSourceMatchedRegion S.hreg S.hcalc S.original1 S.original2
      S.original1_admissible S.original2_admissible := {
    domain := Z
    domain_open := hOpen
    domain_connected := hConn
    domain_room := hRoomZ
    map := Phi
    map_room := hMapRoom
    map_smooth := hSmooth
    map_injective := hInj
    map_jacobian := hJac
    metric_eq := hPull
    source_eq := by
      intro x hx
      funext s
      exact hSources s x hx }
  exact ⟨B,hZ,hContact⟩

/-- An actual contact ball at a frontier point extends the old admissible
match across that point, using the SAME original source family. -/
theorem exists_admissible_source_match_at_contact_frontier
    (S : KnownSideSourceData) (hSep : RadiusTwoSourceSeparation)
    (A : ActualAdmissibleSourceMatch S.hreg S.hcalc S.original1 S.original2
      S.original1_admissible S.original2_admissible)
    (r : ℝ) (hr : 0 < r)
    (hRoom : ball (0 : R3) r ⊆ S.coordinateRoom)
    (hMetric : EqOn S.g1 S.g2 (ball (0 : R3) r))
    (hAll : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      EqOn (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (S.Xi1 z))
        (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
          S.original2_admissible s (S.Xi2 z)) (ball (0 : R3) r))
    (hFrontier : S.Xi2 0 ∈ closure A.domain) :
    ∃ C : ActualAdmissibleSourceMatch S.hreg S.hcalc S.original1 S.original2
        S.original1_admissible S.original2_admissible,
      C.domain = A.domain ∪ (S.Xi2 '' ball (0 : R3) r) ∧
      S.Xi2 0 ∈ C.domain ∧ EqOn C.map A.map A.domain := by
  obtain ⟨B,hBdom,hPoint⟩ :=
    exists_actual_local_source_match_of_ball_all_source_agreement S r hr hRoom hMetric hAll
  have hOverlap : (A.domain ∩ B.domain).Nonempty := by
    have hNhds : B.domain ∈ 𝓝 (S.Xi2 0) := B.domain_open.mem_nhds hPoint
    letI : NeBot (𝓝[A.domain] (S.Xi2 0)) :=
      mem_closure_iff_nhdsWithin_neBot.mp hFrontier
    have hNearB : ∀ᶠ x in 𝓝[A.domain] (S.Xi2 0), x ∈ B.domain :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hNhds
    have hNearA : ∀ᶠ x in 𝓝[A.domain] (S.Xi2 0), x ∈ A.domain :=
      self_mem_nhdsWithin
    obtain ⟨x,hxA,hxB⟩ := (hNearA.and hNearB).exists
    exact ⟨x,hxA,hxB⟩
  obtain ⟨C,hUnion,hOnA,hOnB⟩ :=
    exists_admissible_source_match_union_local S.hreg S.hcalc hSep S.original1
      S.original2 S.original1_admissible S.original2_admissible A B hOverlap
  refine ⟨C, ?_, ?_, hOnA⟩
  · simpa only [hBdom] using hUnion
  · rw [hUnion]
    exact Or.inr hPoint

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
