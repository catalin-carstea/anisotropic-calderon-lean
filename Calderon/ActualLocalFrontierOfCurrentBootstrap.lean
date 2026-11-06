import Calderon.ActualFactoryOneDilationNativeReferenceBaseLift
import Calderon.ActualNormalizedPrincipalMetricRigidity
import Calderon.ActualFrontierAllSourceLocalContinuation
import Calderon.ActualShrinkingRadiusMetricLimit

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ENNReal ContDiff Topology Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource Literature ConnectionError MetricVolume MetricOperator
  ConformalDepth NormalizedPrincipalMetric NormalizedPrincipalMetricSmooth
  ReferenceWeightedApproximation SphereHarmonic DirichletFamily.DriftBootstrap
  ActualScalarPrincipalAdjoint ActualNormalizedSecondMetricDrift CoordinateBootstrapJets
  ExteriorSource.MetricCompatibleSourceJetAlgebra RadiusProfile WeightedBaseSpectral

/-- Actual local frontier data, retaining the full all-radius bootstrap and
one original-coordinate contact ball for metric and all-source equality. -/
structure ActualLocalFrontierOutcome
    (S : KnownSideSourceData) (L lam Rstar eps : ℝ) (p : ℕ) : Prop where
  all_bootstrap : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
    CurrentRadiusBootstrap S L lam delta Rstar eps p
  contact_ball : ∃ r : ℝ, 0 < r ∧ ball (0 : R3) r ⊆ S.coordinateRoom ∧
    EqOn S.g1 S.g2 (ball (0 : R3) r) ∧
    (∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      EqOn (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (S.Xi1 z))
        (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
          S.original2_admissible s (S.Xi2 z)) (ball (0 : R3) r)) ∧
    radiusTwoSourceEvaluationFamily S.hreg S.hcalc S.original1
      S.original1_admissible (S.Xi1 0) =
    radiusTwoSourceEvaluationFamily S.hreg S.hcalc S.original2
      S.original2_admissible (S.Xi2 0)

/-- All-radius current bootstrap closes the actual normalized-principal and
harmonic-coordinate argument on one ball, then extends every original source. -/
theorem actual_local_frontier_of_all_current_radius_bootstrap
    (S : KnownSideSourceData)
    (hFree : ∀ x ∈ S.coordinateRoom,
      S.Xi1 x ∉ closure (fixedExteriorSourceOpens : Set R3) ∧
      S.Xi2 x ∉ closure (fixedExteriorSourceOpens : Set R3))
    (hMatch : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ S.W,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1 S.original1_admissible s (S.Xi1 x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2 S.original2_admissible s (S.Xi2 x))
    (L lam Rstar eps : ℝ) (p : ℕ)
    (hL : 0 < L) (hlam : 0 < lam) (hRstar : 0 < Rstar)
    (heps : 0 < eps) (hp : 1 ≤ p)
    (hAllBoot : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      CurrentRadiusBootstrap S L lam delta Rstar eps p) :
    ActualLocalFrontierOutcome S L lam Rstar eps p := by
  have hBound : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ y ∈ cylinder,
      coordinateH8 (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam) y ≤
        eps * referenceRadius delta Rstar p L y := by
    intro delta hdelta hdeltaOne y hy
    exact (hAllBoot delta hdelta hdeltaOne).1 y hy
  obtain ⟨U,hU,h0,hUCylinder,hZero⟩ :=
    exists_open_neighborhood_zero_of_coordinateH8_forall_delta
      (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam)
      L Rstar eps p hL hRstar.le heps.le hp hBound
  obtain ⟨r,hr,hRoom,hMetric⟩ :=
    exists_ball_metric_eq_of_referenceNormalizedPrincipalDifference_eq_zero
      S L lam hlam U hU h0 hZero
  have hResponses :=
    original_source_responses_eqOn_ball_of_metric_eqOn
      S hFree hMatch r hr hRoom hMetric
  have hEvaluation :=
    original_source_evaluation_family_eq_at_frontier_of_metric_eqOn
      S hFree hMatch r hr hRoom hMetric
  exact ⟨hAllBoot,⟨r,hr,hRoom,hMetric,hResponses,hEvaluation⟩⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
