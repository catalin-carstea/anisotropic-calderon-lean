import Calderon.ContinuousWeakDerivativeClassical

/-! The weak field is used only on its actual open domain. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Metric ContinuousLinearMap TopologicalSpace
open scoped ENNReal ContDiff Convolution Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem eventually_nativeInteriorShrinkingBump_translate_tsupport_subset
    (Ω : Opens R3) (x : R3) (hx : x ∈ Ω) :
    ∀ᶠ p : ℕ × R3 in atTop ×ˢ 𝓝 x,
      ∀ z ∈ tsupport ((nativeInteriorShrinkingBump p.1).normed (volume : Measure R3)),
        p.2 - z ∈ Ω := by
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hx)
  have hε2 : 0 < ε/2 := by linarith
  have hR : ∀ᶠ n : ℕ in atTop, (nativeInteriorShrinkingBump n).rOut < ε/2 :=
    nativeInteriorShrinkingBump_rOut_tendsto.eventually (Iio_mem_nhds hε2)
  have hY : ∀ᶠ y : R3 in 𝓝 x, dist y x < ε/2 :=
    Metric.ball_mem_nhds x hε2
  apply eventually_prod_iff.mpr
  refine ⟨_, hR, _, hY, ?_⟩
  intro n hn y hy z hz
  have hZ : ‖z‖ ≤ (nativeInteriorShrinkingBump n).rOut := by
    rw [(nativeInteriorShrinkingBump n).tsupport_normed_eq] at hz
    simpa only [mem_closedBall, dist_zero_right] using hz
  apply hBall
  change dist (y-z) x < ε
  have hTriangle : dist (y-z) x ≤ ‖z‖ + dist y x := by
    have ht := dist_triangle (y-z) y x
    simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg] using ht
  linarith

theorem hasFDerivAt_of_continuous_weakFDerivOn
    (Ω : Opens R3) (f : R3 → ℝ) (G : R3 → R3 →L[ℝ] ℝ)
    (hf : Continuous f) (hG : Continuous G)
    (hw : TauCeti.HasWeakFDerivOn (volume : Measure R3) Ω f G)
    (x : R3) (hx : x ∈ Ω) : HasFDerivAt f (G x) x := by
  have hD : ∀ᶠ p : ℕ × R3 in atTop ×ˢ 𝓝 x, HasFDerivAt
      ((nativeInteriorShrinkingBump p.1).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] f)
      (((nativeInteriorShrinkingBump p.1).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] G) p.2) p.2 := by
    filter_upwards [eventually_nativeInteriorShrinkingBump_translate_tsupport_subset Ω x hx] with p hp
    have h := hw.hasFDerivAt_convolution_right hf.locallyIntegrable hG.locallyIntegrable
      ((nativeInteriorShrinkingBump p.1).normed (volume : Measure R3))
      (nativeInteriorShrinkingBump p.1).contDiff_normed
      (nativeInteriorShrinkingBump p.1).hasCompactSupport_normed p.2 hp
    rw [convolution_flip, convolution_flip] at h
    exact h
  have hLoc : TendstoLocallyUniformlyOn
      (fun n : ℕ => (nativeInteriorShrinkingBump n).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] G) G atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr
      (normedShrinkingBump_convolution_tendstoLocallyUniformly G hG)
  have hUniform : TendstoUniformlyOnFilter
      (fun n : ℕ => (nativeInteriorShrinkingBump n).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] G) G atTop (𝓝 x) := by
    simpa only [nhdsWithin_univ] using
      (tendstoLocallyUniformlyOn_iff_filter.mp hLoc x (Set.mem_univ x))
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hUniform hD
    (Eventually.of_forall fun y => ContDiffBump.convolution_tendsto_right_of_continuous
      nativeInteriorShrinkingBump_rOut_tendsto hf y)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eventually_nativeInteriorShrinkingBump_translate_tsupport_subset
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasFDerivAt_of_continuous_weakFDerivOn
