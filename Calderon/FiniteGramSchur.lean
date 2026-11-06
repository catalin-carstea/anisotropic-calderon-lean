import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon.SpectralSylvester

lemma finite_gram_schur_quadratic_bound
    {ι α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (φ : ι → α → ℝ)
    (hφ : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun t => φ i t*φ j t) μ)
    (hdiag : ∀ i ∈ s, (∫ t, φ i t*φ i t ∂μ) = 1)
    (S : ι → ι → ℝ) (M : ℝ)
    (hS : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, S i j*x j*y i| ≤
        (M/2) * ((∑ i ∈ s, (x i)^2) + ∑ i ∈ s, (y i)^2))
    (u v : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, (∫ t, φ i t*φ j t ∂μ)*S i j*u j*v i| ≤
      (M/2) * ((∑ i ∈ s, (u i)^2) + ∑ i ∈ s, (v i)^2) := by
  let F : α → ℝ := fun t => ∑ i ∈ s, ∑ j ∈ s,
    (φ i t*φ j t)*(S i j*u j*v i)
  let U : α → ℝ := fun t => ∑ i ∈ s, (φ i t*u i)^2
  let V : α → ℝ := fun t => ∑ i ∈ s, (φ i t*v i)^2
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Integrable (fun t => (φ i t*φ j t)*(S i j*u j*v i)) μ :=
    (hφ i hi j hj).mul_const _
  have hF : Integrable F μ :=
    integrable_finsetSum s fun i hi => integrable_finsetSum s (hterm i hi)
  have henergy (w : ι → ℝ) (i : ι) (hi : i ∈ s) :
      Integrable (fun t => (φ i t*w i)^2) μ := by
    have he : (fun t => (φ i t*w i)^2) = (fun t => (φ i t*φ i t)*(w i)^2) := by
      funext t
      ring
    rw [he]
    exact (hφ i hi i hi).mul_const _
  have hU : Integrable U μ := integrable_finsetSum s (henergy u)
  have hV : Integrable V μ := integrable_finsetSum s (henergy v)
  have hpoint (t : α) : |F t| ≤ (M/2)*(U t+V t) := by
    have he : F t = ∑ i ∈ s, ∑ j ∈ s,
        S i j*(φ j t*u j)*(φ i t*v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [he]
    exact hS (fun i => φ i t*u i) (fun i => φ i t*v i)
  have hleft : (∫ t, F t ∂μ) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ t, φ i t*φ j t ∂μ)*S i j*u j*v i := by
    rw [show (∫ t, F t ∂μ) = ∫ t, ∑ i ∈ s, ∑ j ∈ s,
      (φ i t*φ j t)*(S i j*u j*v i) ∂μ from rfl,
      integral_finsetSum s (fun i hi => integrable_finsetSum s (hterm i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum s (hterm i hi)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const]
    ring
  have henergyIntegral (w : ι → ℝ) :
      (∫ t, ∑ i ∈ s, (φ i t*w i)^2 ∂μ) = ∑ i ∈ s, (w i)^2 := by
    rw [integral_finsetSum s (henergy w)]
    apply Finset.sum_congr rfl
    intro i hi
    have he (t : α) : (φ i t*w i)^2 = (φ i t*φ i t)*(w i)^2 := by ring
    simp_rw [he]
    rw [integral_mul_const,hdiag i hi,one_mul]
  have hbound : |∫ t, F t ∂μ| ≤ ∫ t, (M/2)*(U t+V t) ∂μ :=
    abs_integral_le_integral_abs.trans
      (integral_mono hF.abs ((hU.add hV).const_mul (M/2)) hpoint)
  rw [hleft,integral_const_mul,integral_add hU hV] at hbound
  exact hbound.trans_eq (congrArg (fun z : ℝ => (M/2)*z)
    (congrArg₂ (fun x y : ℝ => x+y) (henergyIntegral u) (henergyIntegral v)))

end OAI.AnisotropicCalderon.SpectralSylvester
