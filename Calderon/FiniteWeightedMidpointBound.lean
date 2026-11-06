import Calderon.FiniteSylvesterFormBound
import Calderon.FiniteWeightedMidpoint

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SpectralSylvester

lemma finite_weighted_midpoint_form_bound
    {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
    (K : ι → ι → ℝ) (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (h0 : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (K i j/(r i*r j))*x j*y i| ≤
        (M0/2)*((∑ i ∈ s, (x i)^2) + ∑ i ∈ s, (y i)^2))
    (h1 : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (r i*K i j/(r j)^3)*x j*y i| ≤
        (M1/2)*((∑ i ∈ s, (x i)^2) + ∑ i ∈ s, (y i)^2))
    (u v : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, (K i j/(r j)^2)*u j*v i| ≤
      ((M0+M1)/2) * Real.sqrt (∑ i ∈ s, u i^2) *
        Real.sqrt (∑ i ∈ s, v i^2) := by
  have hU : 0 ≤ ∑ i ∈ s, u i^2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hV : 0 ≤ ∑ i ∈ s, v i^2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  apply abs_le_half_sqrt_mul_of_quadratic (M0+M1) _ _ _ (add_nonneg hM0 hM1) hU hV
  intro t
  have ht := finite_weighted_midpoint_quadratic_bound s r hr K M0 M1 h0 h1 (fun i => t*u i) v
  have hC : (∑ i ∈ s, ∑ j ∈ s, (K i j/(r j)^2)*(t*u j)*v i) =
      t * (∑ i ∈ s, ∑ j ∈ s, (K i j/(r j)^2)*u j*v i) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hE : (∑ i ∈ s, (t*u i)^2) = t^2 * ∑ i ∈ s, u i^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hC,hE] at ht
  exact (le_abs_self _).trans ht

end OAI.AnisotropicCalderon.SpectralSylvester
