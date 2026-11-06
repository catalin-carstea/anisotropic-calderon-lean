import Calderon.SmoothSobolevBridge
import TauCeti.Analysis.Sobolev.Mollification.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecificLimits.Basic

/-! Full upfront: EXPANSION-continuous-weak-derivative-classical-v001.json.
Explicit mollification derives a classical derivative from continuous weak data.
Actual native compact localization/AE reconstruction remains to be specialized. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Metric ContinuousLinearMap TopologicalSpace
open scoped ENNReal ContDiff Convolution Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def nativeInteriorShrinkingBump (n : ℕ) : ContDiffBump (0 : R3) :=
  ⟨(1 / ((n : ℝ)+1))/2, 1 / ((n : ℝ)+1), by positivity, by
    have h : 0 < 1 / ((n : ℝ)+1) := by positivity
    linarith⟩

theorem nativeInteriorShrinkingBump_rOut_tendsto :
    Tendsto (fun n : ℕ => (nativeInteriorShrinkingBump n).rOut) atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝 (0 : ℝ))
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem normedShrinkingBump_convolution_tendstoLocallyUniformly
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : R3 → E) (hg : Continuous g) :
    TendstoLocallyUniformly
      (fun n : ℕ => (nativeInteriorShrinkingBump n).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] g) g atTop := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro x
  have hφ : Tendsto (fun p : ℕ × R3 => (nativeInteriorShrinkingBump p.1).rOut)
      (atTop ×ˢ 𝓝 x) (𝓝 (0 : ℝ)) :=
    nativeInteriorShrinkingBump_rOut_tendsto.comp tendsto_fst
  have hC : Tendsto (fun p : ℕ × R3 =>
      ((nativeInteriorShrinkingBump p.1).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] g) p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (g x)) :=
    ContDiffBump.convolution_tendsto_right hφ
      (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
      ((hg.tendsto x).comp tendsto_snd) tendsto_snd
  exact ((hg.tendsto x).comp tendsto_snd).prodMk_nhds hC |>.mono_right (nhds_le_uniformity (g x))

theorem hasFDerivAt_of_continuous_weakFDerivOn_top
    (f : R3 → ℝ) (G : R3 → R3 →L[ℝ] ℝ)
    (hf : Continuous f) (hG : Continuous G)
    (hw : TauCeti.HasWeakFDerivOn (volume : Measure R3) (⊤ : Opens R3) f G)
    (x : R3) : HasFDerivAt f (G x) x := by
  have hD (n : ℕ) (y : R3) : HasFDerivAt
      ((nativeInteriorShrinkingBump n).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] f)
      (((nativeInteriorShrinkingBump n).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] G) y) y := by
    have h := hw.hasFDerivAt_convolution_right hf.locallyIntegrable hG.locallyIntegrable
      ((nativeInteriorShrinkingBump n).normed (volume : Measure R3))
      (nativeInteriorShrinkingBump n).contDiff_normed
      (nativeInteriorShrinkingBump n).hasCompactSupport_normed y
      (fun _ _ => Set.mem_univ _)
    rw [convolution_flip, convolution_flip] at h
    exact h
  have hLoc : TendstoLocallyUniformlyOn
      (fun n : ℕ => (nativeInteriorShrinkingBump n).normed (volume : Measure R3)
        ⋆[lsmul ℝ ℝ, (volume : Measure R3)] G) G atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr
      (normedShrinkingBump_convolution_tendstoLocallyUniformly G hG)
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hLoc
    (fun n y _ => hD n y)
    (fun y _ => ContDiffBump.convolution_tendsto_right_of_continuous
      nativeInteriorShrinkingBump_rOut_tendsto hf y) (Set.mem_univ x)

theorem fderiv_eq_of_continuous_weakFDerivOn_top
    (f : R3 → ℝ) (G : R3 → R3 →L[ℝ] ℝ)
    (hf : Continuous f) (hG : Continuous G)
    (hw : TauCeti.HasWeakFDerivOn (volume : Measure R3) (⊤ : Opens R3) f G) :
    fderiv ℝ f = G := by
  funext x
  exact (hasFDerivAt_of_continuous_weakFDerivOn_top f G hf hG hw x).fderiv

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeInteriorShrinkingBump
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeInteriorShrinkingBump_rOut_tendsto
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normedShrinkingBump_convolution_tendstoLocallyUniformly
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasFDerivAt_of_continuous_weakFDerivOn_top
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.fderiv_eq_of_continuous_weakFDerivOn_top
