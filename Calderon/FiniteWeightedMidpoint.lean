import Calderon.FiniteGramSchur
import Calderon.PositiveExponentialGram

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace OAI.AnisotropicCalderon.SpectralSylvester

lemma finite_weighted_midpoint_quadratic_bound
    {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
    (K : ι → ι → ℝ) (M0 M1 : ℝ)
    (h0 : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (K i j/(r i*r j))*x j*y i| ≤
        (M0/2)*((∑ i ∈ s, (x i)^2) + ∑ i ∈ s, (y i)^2))
    (h1 : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (r i*K i j/(r j)^3)*x j*y i| ≤
        (M1/2)*((∑ i ∈ s, (x i)^2) + ∑ i ∈ s, (y i)^2))
    (u v : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, (K i j/(r j)^2)*u j*v i| ≤
      ((M0+M1)/4)*((∑ i ∈ s, (u i)^2) + ∑ i ∈ s, (v i)^2) := by
  let S : ι → ι → ℝ := fun i j =>
    (K i j/(r i*r j) + r i*K i j/(r j)^3)/2
  have hS (x y : ι → ℝ) :
      |∑ i ∈ s, ∑ j ∈ s, S i j*x j*y i| ≤
        (((M0+M1)/2)/2)*((∑ i ∈ s, (x i)^2) + ∑ i ∈ s, (y i)^2) := by
    have he : (∑ i ∈ s, ∑ j ∈ s, S i j*x j*y i) =
        ((∑ i ∈ s, ∑ j ∈ s, (K i j/(r i*r j))*x j*y i) +
          ∑ i ∈ s, ∑ j ∈ s, (r i*K i j/(r j)^3)*x j*y i)/2 := by
      simp only [S,add_div,add_mul,Finset.sum_add_distrib]
      simp_rw [div_mul_eq_mul_div,Finset.sum_div]
    rw [he,abs_div,show |(2:ℝ)|=2 by norm_num]
    have ht := add_le_add (h0 x y) (h1 x y)
    have ha := abs_add_le
      (∑ i ∈ s, ∑ j ∈ s, (K i j/(r i*r j))*x j*y i)
      (∑ i ∈ s, ∑ j ∈ s, (r i*K i j/(r j)^3)*x j*y i)
    nlinarith
  have h := finite_gram_schur_quadratic_bound (volume.restrict (Ioi (0:ℝ))) s
    (fun i t => positiveExponentialVector (r i) t)
    (fun i hi j hj => integrable_positive_exponential_gram (r i) (r j) (hr i hi) (hr j hj))
    (fun i hi => positive_exponential_gram_diagonal (r i) (hr i hi))
    S ((M0+M1)/2) hS u v
  have he : (∑ i ∈ s, ∑ j ∈ s,
      (∫ t : ℝ in Ioi (0:ℝ), positiveExponentialVector (r i) t*positiveExponentialVector (r j) t)*
        S i j*u j*v i) =
      ∑ i ∈ s, ∑ j ∈ s, (K i j/(r j)^2)*u j*v i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_positive_exponential_gram (r i) (r j) (hr i hi) (hr j hj)]
    unfold S
    rw [weighted_midpoint_kernel_identity (r i) (r j) (K i j) (hr i hi) (hr j hj)]
  rw [he] at h
  convert h using 1 <;> ring

end OAI.AnisotropicCalderon.SpectralSylvester
