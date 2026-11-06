import Calderon.FiniteSylvesterFormBound

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SpectralSylvester

lemma finite_sylvester_half_form_bound
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (K : ι → ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (a i^2-a j^2)*K i j*x j*y i| ≤
        (M/2) * ((∑ i ∈ s, (a i*x i)^2) + ∑ i ∈ s, (a i*y i)^2))
    (u v : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*u j*v i| ≤
      (M/2) * Real.sqrt (∑ i ∈ s, a i*u i^2) *
        Real.sqrt (∑ i ∈ s, a i*v i^2) := by
  have hU : 0 ≤ ∑ i ∈ s, a i*u i^2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi).le (sq_nonneg _)
  have hV : 0 ≤ ∑ i ∈ s, a i*v i^2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi).le (sq_nonneg _)
  apply abs_le_half_sqrt_mul_of_quadratic M _ _ _ hM hU hV
  intro t
  have ht := finite_sylvester_quadratic_form_bound s a ha K M hD (fun i => t*u i) v
  have hC : (∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*(t*u j)*v i) =
      t * (∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*u j*v i) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hE : (∑ i ∈ s, a i*(t*u i)^2) = t^2 * ∑ i ∈ s, a i*u i^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hC,hE] at ht
  exact (le_abs_self _).trans ht

end OAI.AnisotropicCalderon.SpectralSylvester
