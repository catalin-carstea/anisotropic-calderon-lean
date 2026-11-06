import Calderon.ActualRadialTestIntegration
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.RadialTestIntegration

/-! Expanded before source in EXPANSION-actual-radial-test-profiles-v001.json. -/

def normSquareRadialProfile (ψ : ℝ → ℝ) (t : ℝ) : ℝ := ψ (Real.sqrt t)

theorem contDiff_normSquareRadialProfile (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (R : ℝ) (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R) :
    ContDiff ℝ ∞ (normSquareRadialProfile ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : Real.sqrt t ∈ tsupport ψ
  · have ht0 : 0 < t := Real.sqrt_pos.mp (hψs ht).1
    exact hψ.contDiffAt.comp t (Real.contDiffAt_sqrt ht0.ne')
  · have hev : ∀ᶠ s in 𝓝 t, normSquareRadialProfile ψ s = 0 := by
      have hs : ∀ᶠ s in 𝓝 t, Real.sqrt s ∉ tsupport ψ :=
        Real.continuous_sqrt.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport ψ).isOpen_compl.mem_nhds ht)
      filter_upwards [hs] with s hs'
      change ψ (Real.sqrt s) = 0
      exact image_eq_zero_of_notMem_tsupport hs'
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

theorem normSquareRadialProfile_zero_of_radius_le (ψ : ℝ → ℝ)
    (R : ℝ) (hR : 0 < R) (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R)
    (t : ℝ) (ht : R^2 ≤ t) : normSquareRadialProfile ψ t = 0 := by
  have hRt : R ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq hR.le]
    exact Real.sqrt_le_sqrt ht
  change ψ (Real.sqrt t) = 0
  exact image_eq_zero_of_notMem_tsupport (fun h => (hψs h).2.not_ge hRt)

theorem normSquareRadialProfile_sq (ψ : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    normSquareRadialProfile ψ (r^2) = ψ r := by
  simp only [normSquareRadialProfile, Real.sqrt_sq hr]

theorem deriv_normSquareRadialProfile_sq (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (R : ℝ) (hψs : tsupport ψ ⊆ Ioo (0 : ℝ) R)
    (r : ℝ) (hr : 0 < r) :
    2 * r * deriv (normSquareRadialProfile ψ) (r^2) = deriv ψ r := by
  have hχ := contDiff_normSquareRadialProfile ψ hψ R hψs
  have hev : (fun s : ℝ => normSquareRadialProfile ψ (s^2)) =ᶠ[𝓝 r] ψ := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    exact normSquareRadialProfile_sq ψ s (le_of_lt hs)
  have hd := (hχ.differentiable (by simp) (r^2)).hasDerivAt.comp r
    (hasDerivAt_pow 2 r)
  have hder : deriv (fun s : ℝ => normSquareRadialProfile ψ (s^2)) r = deriv ψ r :=
    hev.deriv_eq
  change deriv (normSquareRadialProfile ψ ∘ fun s : ℝ => s^2) r = deriv ψ r at hder
  rw [hd.deriv] at hder
  norm_num at hder
  nlinarith [hder]

end OAI.AnisotropicCalderon.RadialTestIntegration

#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.normSquareRadialProfile
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.contDiff_normSquareRadialProfile
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.normSquareRadialProfile_zero_of_radius_le
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.normSquareRadialProfile_sq
#print axioms OAI.AnisotropicCalderon.RadialTestIntegration.deriv_normSquareRadialProfile_sq
