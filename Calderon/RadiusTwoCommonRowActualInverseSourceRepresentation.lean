import Calderon.RadiusTwoCommonLimitInverseRepresentation
import Calderon.RadiusTwoBoundedNormalizedH2Source
import Calderon.NativeInteriorH2ContinuousRepresentative

/-! EXPANSION.json precedes actual discharge of every source-representative input. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCommonSource_limit_actual_inverse_source_representation
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K)) :
    ∀ f : RadiusTwoL2, ∃ F : R3 → ℝ, Continuous F ∧
      (∀ᵐ z ∂(volume : Measure R3).restrict radiusTwoOpens,
        (1/2 : ℝ) • z ∈ closedBall (0 : R3) a →
          F z = TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) z) ∧
      (∫ z in radiusTwoOpens, K z * f z ∂(volume : Measure R3)) = F ((2 : ℝ) • q) := by
  obtain ⟨C,hC,hGain⟩ := exists_uniformly_bounded_normalizedH2_radiusTwoSource hreg g hg
  intro f
  obtain ⟨U,hU,hNorm⟩ := hGain f
  obtain ⟨F0,hF0,hFA⟩ :=
    exists_continuous_representative_on_innerBall_of_nativeH2 hcalc U a ha ha1
  have hPhysical := radiusTwo_continuousRepresentative_transport
    (radiusTwoSourceSolution g hg f) U hU a F0 hF0 hFA
  have hEvaluation := radiusTwoCommonSource_limit_inverse_representation
    g hg a ha ha1 q hq K hLimit f U hU F0 hF0 hFA
  refine ⟨fun z : R3 => F0 ((1/2 : ℝ) • z),hPhysical.1,hPhysical.2,?_⟩
  have hCancel : (1/2 : ℝ) • ((2 : ℝ) • q) = q := by
    rw [smul_smul]
    norm_num
  exact hEvaluation.trans (congrArg F0 hCancel).symm

end OAI.AnisotropicCalderon.ExteriorSource
