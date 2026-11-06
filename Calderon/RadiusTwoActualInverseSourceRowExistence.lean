import Calderon.RadiusTwoCommonDeltaSourceValueLimit
import Calderon.RadiusTwoCommonRowBoundaryContinuousRepresentative
import Calderon.RadiusTwoCommonRowActualInverseSourceRepresentation
import Calderon.RadiusTwoCommonLimitPointSource

/-! EXPANSION.json precedes this actual single-witness inverse-source row bundle. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoActualInverseSourceRow
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a) :
    ∃ K : RadiusTwoL2, ∃ G : R3 → ℝ,
      Tendsto (fun n : ℕ => TauCeti.W1p.value
        (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
          ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
            (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
        atTop (𝓝 K) ∧
      ContinuousOn G (closedBall (0 : R3) 2 \ {(2 : ℝ) • q}) ∧
      G =ᵐ[(volume : Measure R3).restrict ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})]
        (K : R3 → ℝ) ∧
      (∀ y : R3, ‖y‖ = 2 → G y = 0 ∧ ContinuousAt G y) ∧
      (∀ f : RadiusTwoL2, ∃ F : R3 → ℝ, Continuous F ∧
        (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
          (1/2 : ℝ) • z ∈ closedBall (0 : R3) a →
            F z = TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) z) ∧
        (∫ z in radiusTwoOpens, K z * f z ∂(volume : Measure R3)) = F ((2 : ℝ) • q)) ∧
      (∀ φ : 𝓓(radiusTwoOpens, ℝ),
        (∫ z in radiusTwoOpens, K z * (radiusTwoCompactMetricTestDensity g hg φ).1 z
          ∂(volume : Measure R3)) = φ ((2 : ℝ) • q)) := by
  trace "PROOFENTER actual single-witness inverse-source row existence"
  obtain ⟨K,hLimit⟩ := exists_radiusTwoCommonDeltaSource_value_limit hreg hcalc g hg a ha ha1 q hq
  trace "ACTUAL COMMON SOURCE LIMIT CHOSEN ONCE"
  obtain ⟨G,hCont,hRep,hBoundary⟩ :=
    BoundaryBarrier.exists_radiusTwoCommonRow_boundary_continuous_representative
      hreg hcalc g hg a ha ha1 q hq K hLimit
  refine ⟨K,G,hLimit,hCont,hRep,hBoundary,?_,?_⟩
  · exact radiusTwoCommonSource_limit_actual_inverse_source_representation
      hreg hcalc g hg a ha ha1 q hq K hLimit
  · exact radiusTwoCommonSource_limit_pointSource g hg a ha ha1 q hq K hLimit

end OAI.AnisotropicCalderon.ExteriorSource
