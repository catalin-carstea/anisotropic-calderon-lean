import Calderon.ActualOriginalSourceResponseCoordinatePDE
import Calderon.ActualGlobalNativeDensityPairedReproduction
import Calderon.ActualKnownSideInteriorSeed
import Calderon.ActualNormalizedPrincipalMetricRigidity
import Calderon.ActualNormalizedSecondUCPDictionary
import Calderon.CollaboratorUniqueContinuationProofOct17
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource MetricOperator MetricVolume ConnectionError
  ConformalDepth ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric RadiusProfile
  CoordinateBootstrapJets

/-- Equality of the actual coordinate metrics across a contact ball propagates
the original response equality for every exterior source on that same ball. -/
theorem original_source_responses_eqOn_ball_of_metric_eqOn
    (S : KnownSideSourceData)
    (hFree : ∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3))
    (hMatch : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
        (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
        (S.Xi2 x))
    (r : ℝ) (hr : 0 < r) (hRoom : ball (0 : R3) r ⊆ S.coordinateRoom)
    (hMetric : EqOn S.g1 S.g2 (ball (0 : R3) r)) :
    ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      EqOn (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (S.Xi1 z))
        (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
          S.original2_admissible s (S.Xi2 z)) (ball (0 : R3) r) := by
  intro s
  let v1 : R3 → ℝ := fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc
    S.original1 S.original1_admissible s (S.Xi1 z)
  let v2 : R3 → ℝ := fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc
    S.original2 S.original2_admissible s (S.Xi2 z)
  let B : Set R3 := ball (0 : R3) r
  let A : R3 → Matrix (Fin 3) (Fin 3) ℝ := principalCoefficient S.g1
  have hA : ContDiff ℝ ∞ A := by
    apply contDiff_principalCoefficient_of_smooth_posDef S.g1
    · exact S.g1_admissible.smooth
    · exact S.g1_admissible.posDef
  have hAentries : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun z => A z i j) := by
    intro i j
    exact (contDiff_pi.mp (contDiff_pi.mp hA i) j)
  have hApos : ∀ x : R3, (A x).PosDef := by
    intro x
    have hv : 0 < vol S.g1 x := vol_pos_of_posDef S.g1 S.g1_admissible.posDef x
    exact (S.g1_admissible.posDef x).inv.smul hv
  have hV1 : ContDiffOn ℝ ∞ v1 B :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original1
      S.original1_admissible s).2.1.comp S.Xi1_smooth S.Xi1_room).mono hRoom
  have hV2 : ContDiffOn ℝ ∞ v2 B :=
    ((radiusTwoSmoothSourceResponse_spec S.hreg S.hcalc S.original2
      S.original2_admissible s).2.1.comp S.Xi2_smooth S.Xi2_room).mono hRoom
  have hPDE1 : ∀ x ∈ B, divCoeffGrad A v1 x = 0 := by
    intro x hx
    have hOutside : S.Xi1 x ∉ tsupport s := by
      intro h
      exact (hFree x (hRoom hx)).1 (subset_closure (s.tsupport_subset h))
    have h := coordinateFluxDivergence_originalSourceResponse_pullback_eq_zero
      S.hreg S.hcalc S.original1 S.g1 S.original1_admissible
      S.coordinateRoom S.coordinateRoom_open S.Xi1 S.Xi1_smooth S.Xi1_room
      S.Xi1_jacobian S.carrier1 s x (hRoom hx) hOutside
    rw [coordinateFluxDivergence_metric_eq_divCoeffGrad] at h
    exact h
  have hPDE2 : ∀ x ∈ B, divCoeffGrad A v2 x = 0 := by
    intro x hx
    have hOutside : S.Xi2 x ∉ tsupport s := by
      intro h
      exact (hFree x (hRoom hx)).2 (subset_closure (s.tsupport_subset h))
    have h := coordinateFluxDivergence_originalSourceResponse_pullback_eq_zero
      S.hreg S.hcalc S.original2 S.g2 S.original2_admissible
      S.coordinateRoom S.coordinateRoom_open S.Xi2 S.Xi2_smooth S.Xi2_room
      S.Xi2_jacobian S.carrier2 s x (hRoom hx) hOutside
    have hGerm : S.g2 =ᶠ[𝓝 x] S.g1 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with z hz
      exact (hMetric hz).symm
    have hSame := coordinateFluxDivergence_metricDivergenceFlux_congr_metric_of_eventuallyEq
      S.g2 S.g1 v2 x hGerm
    rw [coordinateFluxDivergence_metric_eq_divCoeffGrad] at h
    rw [coordinateFluxDivergence_metric_eq_divCoeffGrad,
      coordinateFluxDivergence_metric_eq_divCoeffGrad] at hSame
    exact hSame.symm.trans h
  have hDiff : ∀ x ∈ B, divCoeffGrad A (fun z => v1 z - v2 z) x = 0 := by
    intro x hx
    rw [pairedReproduction_divCoeffGrad_sub_of_isOpen A hAentries B isOpen_ball
      v1 v2 hV1 hV2 x hx, hPDE1 x hx, hPDE2 x hx, sub_self]
  let V : Set R3 := B ∩ S.W
  have hVopen : IsOpen V := isOpen_ball.inter S.W_open
  have hVne : V.Nonempty := by
    obtain ⟨x,hxB,hxW⟩ := known_side_seed_nonempty_in_open_neighborhood S 1
      (by norm_num) B isOpen_ball (mem_ball_self hr)
    exact ⟨x,hxB,by simpa using hxW⟩
  have hVsub : V ⊆ B := inter_subset_left
  have hVzero : ∀ x ∈ V, v1 x - v2 x = 0 := by
    intro x hx
    exact sub_eq_zero.mpr (hMatch s x hx.2)
  have hConn : IsConnected B :=
    (convex_ball (0 : R3) r).isConnected ⟨0, mem_ball_self hr⟩
  have hZero := uniqueContinuation B isOpen_ball hConn A hA.contDiffOn
    (fun x _ => hApos x) (fun z => v1 z - v2 z) (hV1.sub hV2)
    hDiff V hVopen hVne hVsub hVzero
  intro x hx
  exact sub_eq_zero.mp (hZero x hx)

/-- The local all-source response equality gives the original source-family
partner equality at the contact center, not merely five selected tests. -/
theorem original_source_evaluation_family_eq_at_frontier_of_metric_eqOn
    (S : KnownSideSourceData)
    (hFree : ∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3))
    (hMatch : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
        (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
        (S.Xi2 x))
    (r : ℝ) (hr : 0 < r) (hRoom : ball (0 : R3) r ⊆ S.coordinateRoom)
    (hMetric : EqOn S.g1 S.g2 (ball (0 : R3) r)) :
    radiusTwoSourceEvaluationFamily S.hreg S.hcalc S.original1
      S.original1_admissible (S.Xi1 0) =
    radiusTwoSourceEvaluationFamily S.hreg S.hcalc S.original2
      S.original2_admissible (S.Xi2 0) := by
  funext s
  exact original_source_responses_eqOn_ball_of_metric_eqOn S hFree hMatch r hr hRoom
    hMetric s (mem_ball_self hr)

/-- The exact compact strict-improvement inputs already used by the native
metric-rigidity theorem produce equality of every original source response on
the resulting contact ball and the original source-family partner at its center. -/
theorem exists_ball_original_source_responses_eq_of_compact_strict_improvement
    (S : KnownSideSourceData)
    (hFree : ∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3))
    (hMatch : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s
        (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s
        (S.Xi2 x))
    (L lam R eps : ℝ) (p : ℕ) (K : Set R3) (hK : IsCompact K)
    (hlam : 0 < lam) (hL : 0 < L) (hR : 0 < R) (heps : 0 < eps) (hp : 1 ≤ p)
    (hInitial : ∀ x ∈ K,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        eps * referenceRadius 1 R p L x)
    (hImprove : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      (∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        eps * referenceRadius delta R p L x) →
      ∀ x ∈ K, coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        (eps/2) * referenceRadius delta R p L x)
    (hOff : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ cylinder, x ∉ K →
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) x ≤
        eps * referenceRadius delta R p L x) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ S.coordinateRoom ∧
      EqOn S.g1 S.g2 (ball (0 : R3) r) ∧
      (∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        EqOn (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
          S.original1_admissible s (S.Xi1 z))
          (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
            S.original2_admissible s (S.Xi2 z)) (ball (0 : R3) r)) ∧
      radiusTwoSourceEvaluationFamily S.hreg S.hcalc S.original1
        S.original1_admissible (S.Xi1 0) =
      radiusTwoSourceEvaluationFamily S.hreg S.hcalc S.original2
        S.original2_admissible (S.Xi2 0) := by
  obtain ⟨r, hr, hRoom, hMetric⟩ :=
    exists_ball_metric_eq_of_compact_strict_improvement S L lam R eps p K hK
      hlam hL hR heps hp hInitial hImprove hOff
  refine ⟨r, hr, hRoom, hMetric, ?_, ?_⟩
  · exact original_source_responses_eqOn_ball_of_metric_eqOn S hFree hMatch r hr
      hRoom hMetric
  · exact original_source_evaluation_family_eq_at_frontier_of_metric_eqOn S hFree
      hMatch r hr hRoom hMetric

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
