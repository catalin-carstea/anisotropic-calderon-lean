import Calderon.LocalAEContinuousRepresentativeGluing
import Calderon.RadiusTwoCommonRowLocalContinuousRepresentative

/-! Full EXPANSION.json precedes actual punctured-ball continuity for the SAME row. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

theorem exists_radiusTwoCommonRow_continuous_representative
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K)) :
    ∃ F : R3 → ℝ,
      ContinuousOn F ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) ∧
      F =ᵐ[(volume : Measure R3).restrict ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})]
        (K : R3 → ℝ) := by
  have hNOpen : IsOpen (radiusTwoOpens : Set R3) := by
    change IsOpen (ball (0 : R3) 2)
    exact isOpen_ball
  apply ContinuousRepresentative.exists_continuousOn_representative_of_locally_ae
    (volume : Measure R3) ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})
    (IsOpen.sdiff hNOpen isClosed_singleton) (K : R3 → ℝ)
  intro x hx
  exact exists_radiusTwoCommonRow_local_continuous_representative
    hreg hcalc g hg a ha ha1 q hq K hLimit x hx

end OAI.AnisotropicCalderon.ExteriorSource
