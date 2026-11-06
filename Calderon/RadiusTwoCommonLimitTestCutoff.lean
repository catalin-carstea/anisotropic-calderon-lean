import Calderon.RadiusTwoCommonLimitZeroCutoff

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoCommonLimit_test_cutoff
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (η : 𝓓(radiusTwoOpens, ℝ)) (hPole : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ)) :
    ∃ w : RadiusTwoH1Zero,
      (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z : R3 => η z * K z) := by
  trace "PROOF ENTER actual SAME-row test cutoff"
  obtain ⟨M,hM,hAbs,hGrad⟩ :=
    (η.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le η.hasCompactSupport
  have hVan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : R3,
      dist ((1/2 : ℝ) • z) q < δ → η z = 0 := by
    have hZero : (η : R3 → ℝ) =ᶠ[𝓝 ((2 : ℝ) • q)] (0 : R3 → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hPole
    have hComp := hZero.comp_tendsto ((continuous_const_smul (2 : ℝ)).tendsto q)
    have hNear : ∀ᶠ y in 𝓝 q, η ((2 : ℝ) • y) = 0 := by
      filter_upwards [hComp] with y hy
      change η ((2 : ℝ) • y) = 0 at hy
      exact hy
    obtain ⟨δ,hδ,hδZero⟩ := Metric.mem_nhds_iff.mp hNear
    refine ⟨δ,hδ,?_⟩
    intro z hz
    have hy : (1/2 : ℝ) • z ∈ ball q δ := hz
    have h := hδZero hy
    have hCancel : (2 : ℝ) • ((1/2 : ℝ) • z) = z := by
      rw [smul_smul]
      norm_num
    change η ((2 : ℝ) • ((1/2 : ℝ) • z)) = 0 at h
    rw [hCancel] at h
    exact h
  trace "ACTUAL BOUNDS VANISHING MADE SAME-row test cutoff"
  exact exists_radiusTwoCommonLimit_zero_cutoff g hg a ha ha1 q hq K hLimit
    ⟨η,η.contDiff⟩ η.hasCompactSupport M hM hAbs hGrad hVan

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoCommonLimit_test_cutoff
