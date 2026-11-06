import Calderon.AngularEuclideanDensity
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.BaseDensityAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual Frechet directional derivative in a fixed base direction. -/
def directionalDeriv (v : R3) (u : R3 → E) : R3 → E :=
  fun x => fderiv ℝ u x v

lemma contDiff_directionalDeriv (v : R3) (u : R3 → E) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (directionalDeriv v u) := by
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma hasCompactSupport_directionalDeriv (v : R3) (u : R3 → E)
    (hc : HasCompactSupport u) : HasCompactSupport (directionalDeriv v u) := by
  exact hc.fderiv_apply (𝕜 := ℝ) v

lemma compact_inner_integrable (f g : R3 → E) (hf : Continuous f)
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) := by
  apply (hf.inner hg).integrable_of_hasCompactSupport
  apply hc.mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  contrapose! hx
  simp [hx]

/-- Actual base integration by parts for a real Hilbert-valued compact section. -/
theorem compact_inner_directionalDeriv (v : R3) (f g : R3 → E)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (∫ x : R3, ⟪f x, directionalDeriv v g x⟫_ℝ) =
      -(∫ x : R3, ⟪directionalDeriv v f x, g x⟫_ℝ) := by
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerSL ℝ (E := E))
  · exact compact_inner_integrable _ g
      (contDiff_directionalDeriv v f hf).continuous hg.continuous hc
  · exact compact_inner_integrable f _ hf.continuous
      (contDiff_directionalDeriv v g hg).continuous
      (hasCompactSupport_directionalDeriv v g hc)
  · exact compact_inner_integrable f g hf.continuous hg.continuous hc
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hg.differentiable (by simp) x

/-- The full scalar density stays inside the derivative on the adjoint side. -/
theorem compact_weighted_first_adjoint (v : R3) (mu a : R3 → ℝ)
    (u w : R3 → E) (hm : ContDiff ℝ ∞ mu) (ha : ContDiff ℝ ∞ a)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u) :
    (∫ x : R3, mu x * a x * ⟪directionalDeriv v u x, w x⟫_ℝ) =
      -(∫ x : R3, ⟪directionalDeriv v (fun y => (mu y * a y) • w y) x,
        u x⟫_ℝ) := by
  have h := compact_inner_directionalDeriv v (fun y => (mu y * a y) • w y) u
    ((hm.mul ha).smul hw) hu hc
  simpa only [inner_smul_left, starRingEnd_apply, star_trivial, real_inner_comm] using h

/-- Twice integrated genuine second-base term; the adjoint order is reversed. -/
theorem compact_weighted_second_adjoint (i j : R3) (mu a : R3 → ℝ)
    (u w : R3 → E) (hm : ContDiff ℝ ∞ mu) (ha : ContDiff ℝ ∞ a)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport u) :
    (∫ x : R3, mu x * a x *
      ⟪directionalDeriv i (directionalDeriv j u) x, w x⟫_ℝ) =
      (∫ x : R3, ⟪directionalDeriv j
        (directionalDeriv i (fun y => (mu y * a y) • w y)) x, u x⟫_ℝ) := by
  have h1 := compact_weighted_first_adjoint i mu a (directionalDeriv j u) w hm ha
    (contDiff_directionalDeriv j u hu) hw (hasCompactSupport_directionalDeriv j u hc)
  have h2 := compact_inner_directionalDeriv j
    (directionalDeriv i (fun y => (mu y * a y) • w y)) u
    (contDiff_directionalDeriv i _ ((hm.mul ha).smul hw)) hu hc
  rw [h1, h2, neg_neg]

lemma directionalDeriv_smul (v : R3) (c : R3 → ℝ) (w : R3 → E)
    (hc : ContDiff ℝ ∞ c) (hw : ContDiff ℝ ∞ w) (x : R3) :
    directionalDeriv v (fun y => c y • w y) x =
      directionalDeriv v c x • w x + c x • directionalDeriv v w x := by
  unfold directionalDeriv
  rw [fderiv_fun_smul (hc.differentiable (by simp) x) (hw.differentiable (by simp) x)]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  exact add_comm _ _

end OAI.AnisotropicCalderon.BaseDensityAdjoint
