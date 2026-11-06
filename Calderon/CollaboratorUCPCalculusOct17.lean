import Calderon.CollaboratorUniqueContinuationDefinitionOct17
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Coordinate calculus on `R3` for the Carleman estimate

Partial derivatives `pd i f x = fderiv ℝ f x (single i 1)` of smooth real functions on `R3`,
their algebraic rules, symmetry of second derivatives and the vanishing of integrals of
derivatives of compactly supported functions. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace OAI.AnisotropicCalderon

/-- Coordinate partial derivative on `R3`. -/
def pd (i : Fin 3) (f : R3 → ℝ) (x : R3) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

section
variable {f g : R3 → ℝ} {i j : Fin 3}

@[fun_prop]
theorem contDiff_pd (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pd i f) := by
  unfold pd
  have h := hf.fderiv_right (m := ∞) (by simp)
  exact h.clm_apply contDiff_const

@[fun_prop]
theorem contDiff_pd_apply (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => pd i f x) :=
  contDiff_pd hf

theorem diffAt (hf : ContDiff ℝ ∞ f) (x : R3) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)) x

theorem pd_add (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    pd i (fun y => f y + g y) x = pd i f x + pd i g x := by
  simp [pd, fderiv_fun_add (diffAt hf x) (diffAt hg x)]

theorem pd_sub (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp [pd, fderiv_fun_sub (diffAt hf x) (diffAt hg x)]

theorem pd_neg (x : R3) : pd i (fun y => -f y) x = -pd i f x := by
  simp [pd, fderiv_fun_neg]

theorem pd_mul (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : R3) :
    pd i (fun y => f y * g y) x = pd i f x * g x + f x * pd i g x := by
  simp [pd, fderiv_fun_mul (diffAt hf x) (diffAt hg x)]
  ring

theorem pd_const (c : ℝ) (x : R3) : pd i (fun _ => c) x = 0 := by
  simp [pd]

theorem pd_const_mul (c : ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    pd i (fun y => c * f y) x = c * pd i f x := by
  rw [pd_mul contDiff_const hf, pd_const]; ring

theorem pd_exp (hf : ContDiff ℝ ∞ f) (x : R3) :
    pd i (fun y => Real.exp (f y)) x = Real.exp (f x) * pd i f x := by
  simp [pd, fderiv_exp (diffAt hf x)]

theorem pd_sum {F : Fin 3 → R3 → ℝ} (hF : ∀ k, ContDiff ℝ ∞ (F k)) (x : R3) :
    pd i (fun y => ∑ k, F k y) x = ∑ k, pd i (F k) x := by
  unfold pd
  rw [fderiv_fun_sum (fun k _ => diffAt (hF k) x)]
  simp

theorem pd_comm (hf : ContDiff ℝ ∞ f) :
    pd i (pd j f) = pd j (pd i f) := by
  funext x
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have key : ∀ a b : Fin 3, pd a (pd b f) x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b
    unfold pd
    have h2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
      ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
    rw [fderiv_clm_apply h2 (differentiableAt_const _)]
    simp
  rw [key, key, hs]

theorem hasCompactSupport_pd (hf : HasCompactSupport f) : HasCompactSupport (pd i f) :=
  hf.fderiv_apply (𝕜 := ℝ) _

theorem integrable_of_contDiff_hasCompactSupport (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hc

theorem integral_pd_eq_zero (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∫ x, pd i f x = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : R3 => (1 : ℝ)) (g := f) (v := EuclideanSpace.single i 1)
    (by simp) (by simp only [one_mul]; exact (integrable_of_contDiff_hasCompactSupport
      (contDiff_pd hf) (hasCompactSupport_pd (i := i) hc)))
    (by simpa using integrable_of_contDiff_hasCompactSupport hf hc)
    (fun x _ => differentiableAt_const _) (fun x _ => diffAt hf x)
  simpa [pd] using h

end

end OAI.AnisotropicCalderon
