import Calderon.RadiusTwoCommonRowActualInverseSourceRepresentation
import Calderon.LocalAEContinuousRepresentativeGluing

/-! Full EXPANSION.json precedes the actual local inverse-pairing consequences. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

variable (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
include hreg hcalc hg ha ha1 hq hLimit

theorem radiusTwoCommonSource_inverse_pairing_eq_local_continuous_rep
    (f : RadiusTwoL2) (V : Set R3) (hV : IsOpen V)
    (hqV : (2 : ℝ) • q ∈ V) (hRoom : V ⊆ ball (0 : R3) (2*a))
    (G : R3 → ℝ) (hG : ContinuousOn G V)
    (hRep : (TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict V] G) :
    (∫ z in radiusTwoOpens, K z * f z ∂(volume : Measure R3)) = G ((2 : ℝ) • q) := by
  obtain ⟨F,hF,hFA,hPair⟩ := radiusTwoCommonSource_limit_actual_inverse_source_representation
    hreg hcalc g hg a ha ha1 q hq K hLimit f
  have hVN : V ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    change z ∈ ball (0 : R3) 2
    exact ball_subset_ball (by linarith : 2*a ≤ 2) (hRoom hz)
  have hFilter : ae ((volume : Measure R3).restrict V) ≤
      ae ((volume : Measure R3).restrict radiusTwoOpens) :=
    ae_mono (Measure.restrict_mono_set volume hVN)
  have hHalf (z : R3) (hz : z ∈ V) : (1/2 : ℝ) • z ∈ closedBall (0 : R3) a := by
    apply mem_closedBall.mpr
    rw [dist_zero_right]
    have hNorm : ‖(1/2 : ℝ) • z‖ = (1/2 : ℝ) * ‖z‖ := by
      rw [norm_smul]
      norm_num
    rw [hNorm]
    have hzNorm : ‖z‖ < 2*a := mem_ball_zero_iff.mp (hRoom hz)
    linarith
  have hAE : F =ᵐ[(volume : Measure R3).restrict V] G := by
    filter_upwards [hFA.filter_mono hFilter,hRep,ae_restrict_mem hV.measurableSet]
      with z hzF hzG hzV
    exact (hzF (hHalf z hzV)).trans hzG
  have hEq : EqOn F G V := Measure.eqOn_open_of_ae_eq hAE hV hF.continuousOn hG
  exact hPair.trans (hEq hqV)

theorem radiusTwoCommonSource_inverse_pairings_eq_of_local_source_values_eq
    (f h : RadiusTwoL2) (V : Set R3) (hV : IsOpen V)
    (hqV : (2 : ℝ) • q ∈ V) (hRoom : V ⊆ ball (0 : R3) (2*a))
    (hValues : (TauCeti.W1p.value (radiusTwoSourceSolution g hg f : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict V]
        (TauCeti.W1p.value (radiusTwoSourceSolution g hg h : RadiusTwoH1) : R3 → ℝ)) :
    (∫ z in radiusTwoOpens, K z * f z ∂(volume : Measure R3)) =
      ∫ z in radiusTwoOpens, K z * h z ∂(volume : Measure R3) := by
  obtain ⟨F,hF,hFA,hPair⟩ := radiusTwoCommonSource_limit_actual_inverse_source_representation
    hreg hcalc g hg a ha ha1 q hq K hLimit f
  have hVN : V ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    change z ∈ ball (0 : R3) 2
    exact ball_subset_ball (by linarith : 2*a ≤ 2) (hRoom hz)
  have hFilter : ae ((volume : Measure R3).restrict V) ≤
      ae ((volume : Measure R3).restrict radiusTwoOpens) :=
    ae_mono (Measure.restrict_mono_set volume hVN)
  have hRepH : (TauCeti.W1p.value (radiusTwoSourceSolution g hg h : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict V] F := by
    filter_upwards [hFA.filter_mono hFilter,hValues,ae_restrict_mem hV.measurableSet]
      with z hzF hzVal hzV
    have hHalf : (1/2 : ℝ) • z ∈ closedBall (0 : R3) a := by
      apply mem_closedBall.mpr
      rw [dist_zero_right]
      have hNorm : ‖(1/2 : ℝ) • z‖ = (1/2 : ℝ) * ‖z‖ := by
        rw [norm_smul]
        norm_num
      rw [hNorm]
      have hzNorm : ‖z‖ < 2*a := mem_ball_zero_iff.mp (hRoom hzV)
      linarith
    exact hzVal.symm.trans (hzF hHalf).symm
  have hOther := radiusTwoCommonSource_inverse_pairing_eq_local_continuous_rep
    hreg hcalc g hg a ha ha1 q hq K hLimit h V hV hqV hRoom F hF.continuousOn hRepH
  exact hPair.trans hOther.symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoCommonSource_inverse_pairing_eq_local_continuous_rep
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoCommonSource_inverse_pairings_eq_of_local_source_values_eq
