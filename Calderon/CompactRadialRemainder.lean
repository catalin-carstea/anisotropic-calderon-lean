import Calderon.SignedQuadraticRemainder
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def radialFirstDerivative (F : P × ℝ → V) (p : P × ℝ) : V :=
  fderiv ℝ F p (0,1)

def radialSecondDerivative (F : P × ℝ → V) (p : P × ℝ) : V :=
  fderiv ℝ (radialFirstDerivative F) p (0,1)

theorem contDiff_radialFirstDerivative (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialFirstDerivative F) :=
  (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_radialSecondDerivative (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialSecondDerivative F) :=
  ((contDiff_radialFirstDerivative F hF).fderiv_right (by simp)).clm_apply contDiff_const

theorem deriv_radialSlice (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    deriv (fun t : ℝ => F (p,t)) r = radialFirstDerivative F (p,r) := by
  have hc : HasDerivAt (fun t : ℝ => (p,t)) (0,1) r :=
    (hasDerivAt_const r p).prodMk (hasDerivAt_id r)
  have hd := (hF.differentiable (by simp) (p,r)).hasFDerivAt.comp_hasDerivAt r hc
  simpa only [Function.comp_def,radialFirstDerivative] using hd.deriv

theorem deriv_deriv_radialSlice (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    deriv (deriv (fun t : ℝ => F (p,t))) r = radialSecondDerivative F (p,r) := by
  have he : deriv (fun t : ℝ => F (p,t)) = fun t => radialFirstDerivative F (p,t) := by
    funext t
    exact deriv_radialSlice F hF p t
  rw [he]
  exact deriv_radialSlice (radialFirstDerivative F) (contDiff_radialFirstDerivative F hF) p r

theorem exists_compact_uniform_radial_quadratic_bound (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (q : Set P) (hq : IsCompact q) (δ : ℝ) (hδ : 0 ≤ δ)
    (hzero : ∀ p ∈ q, HasDerivAt (fun t : ℝ => F (p,t)) 0 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ q, ∀ r : ℝ, |r| ≤ δ → ‖F (p,r) - F (p,0)‖ ≤ B * r^2 := by
  obtain ⟨C,hC⟩ := (hq.prod (isCompact_Icc : IsCompact (Icc (-δ) δ))).exists_bound_of_continuousOn
    (contDiff_radialSecondDerivative F hF).continuous.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p hp r hr
  have hs : ContDiff ℝ ∞ (fun t : ℝ => F (p,t)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hb (t : ℝ) (ht : |t| ≤ δ) : ‖deriv (deriv (fun u : ℝ => F (p,u))) t‖ ≤ max C 0 := by
    rw [deriv_deriv_radialSlice F hF p t]
    exact (hC (p,t) ⟨hp,abs_le.mp ht⟩).trans (le_max_left _ _)
  exact norm_sub_le_quadratic_of_second_deriv_le _ hs δ (max C 0) hδ
    (le_max_right _ _) (hzero p hp) hb r hr
end OAI.AnisotropicCalderon.ConnectionError
