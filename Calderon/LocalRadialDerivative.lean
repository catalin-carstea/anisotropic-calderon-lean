import Calderon.ActualNativeTraceOperatorFamily
import Calderon.CompactRadialRemainder
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiffAt_radialFirstDerivative (F : P × ℝ → V) (p : P × ℝ)
    (hF : ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (radialFirstDerivative F) p :=
  (hF.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem contDiffAt_radialSecondDerivative (F : P × ℝ → V) (p : P × ℝ)
    (hF : ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (radialSecondDerivative F) p :=
  ((contDiffAt_radialFirstDerivative F p hF).fderiv_right (by simp)).clm_apply contDiffAt_const

theorem deriv_radialSlice_of_differentiableAt (F : P × ℝ → V) (y : P) (r : ℝ)
    (hF : DifferentiableAt ℝ F (y,r)) :
    deriv (fun t : ℝ => F (y,t)) r = radialFirstDerivative F (y,r) := by
  have hc : HasDerivAt (fun t : ℝ => (y,t)) (0,1) r :=
    (hasDerivAt_const r y).prodMk (hasDerivAt_id r)
  simpa only [Function.comp_def,radialFirstDerivative] using
    (hF.hasFDerivAt.comp_hasDerivAt r hc).deriv

theorem deriv_deriv_radialSlice_of_contDiffAt (F : P × ℝ → V) (y : P) (r : ℝ)
    (hF : ContDiffAt ℝ ∞ F (y,r)) :
    deriv (deriv (fun t : ℝ => F (y,t))) r = radialSecondDerivative F (y,r) := by
  have hNearby : ∀ᶠ p in 𝓝 (y,r), DifferentiableAt ℝ F p := by
    filter_upwards [(hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with p hp
    exact hp.differentiableAt (by norm_num)
  have hNearbySlice := (continuous_const.prodMk continuous_id).continuousAt.eventually hNearby
  have he : deriv (fun t : ℝ => F (y,t)) =ᶠ[𝓝 r]
      (fun t : ℝ => radialFirstDerivative F (y,t)) := by
    filter_upwards [hNearbySlice] with t ht
    exact deriv_radialSlice_of_differentiableAt F y t ht
  rw [he.deriv_eq]
  exact deriv_radialSlice_of_differentiableAt (radialFirstDerivative F) y r
    ((contDiffAt_radialFirstDerivative F (y,r) hF).differentiableAt (by simp))

end OAI.AnisotropicCalderon.ConnectionError
