import Calderon.RadiusTwoNativeSourceSolution
import Calderon.RadiusTwoNativeL2Dilation
import Calderon.NativeSmoothBallSobolev

/-! Full EXPANSION.json precedes literal smooth forcing normalization at every actual order. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily

def radiusTwoNormalizedSmoothForcing (F : SmoothData) : SmoothData :=
  ⟨(fun x : R3 => (4 : ℝ) * F.1 ((2 : ℝ) • x)),
    by
      have hScale : ContDiff ℝ ∞ (fun x : R3 => (2 : ℝ) • x) := contDiff_const_smul 2
      exact contDiff_const.mul (F.2.comp hScale)⟩

lemma value_radiusTwoNormalizedSmoothForcing (s : ℕ) (F : SmoothData) :
    TauCeti.Wkp.value s (smoothBallSobolev s (radiusTwoNormalizedSmoothForcing F)) =
      (4 : ℝ) • radiusTwoNativeL2Dilation (smoothRadiusTwoForcing F) := by
  apply Lp.ext
  filter_upwards [value_smoothBallSobolev_ae s (radiusTwoNormalizedSmoothForcing F),
    Lp.coeFn_smul (4 : ℝ) (radiusTwoNativeL2Dilation (smoothRadiusTwoForcing F)),
    radiusTwoNativeL2Dilation_apply_ae (smoothRadiusTwoForcing F),
    quasiMeasurePreserving_radiusTwo_comp_two.ae_eq_comp (smoothRadiusTwoForcing_ae F)]
      with x hF hSmul hDil hComp
  change TauCeti.Wkp.value s (smoothBallSobolev s (radiusTwoNormalizedSmoothForcing F)) x =
    (4 : ℝ) * F.1 ((2 : ℝ) • x) at hF
  change smoothRadiusTwoForcing F ((2 : ℝ) • x) = F.1 ((2 : ℝ) • x) at hComp
  change ((4 : ℝ) • radiusTwoNativeL2Dilation (smoothRadiusTwoForcing F)) x =
    4 * radiusTwoNativeL2Dilation (smoothRadiusTwoForcing F) x at hSmul
  calc
    _ = (4 : ℝ) * F.1 ((2 : ℝ) • x) := hF
    _ = 4 * smoothRadiusTwoForcing F ((2 : ℝ) • x) := congrArg (fun t : ℝ => 4*t) hComp.symm
    _ = 4 * radiusTwoNativeL2Dilation (smoothRadiusTwoForcing F) x :=
      congrArg (fun t : ℝ => 4*t) hDil.symm
    _ = _ := hSmul.symm

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.radiusTwoNormalizedSmoothForcing
#print axioms OAI.AnisotropicCalderon.ExteriorSource.value_radiusTwoNormalizedSmoothForcing
