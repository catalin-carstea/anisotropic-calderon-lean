import Calderon.SpectralSylvesterIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace OAI.AnisotropicCalderon.SpectralSylvester

variable {ι : Type*}

lemma integrable_finite_sylvester_kernel
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (K : ι → ι → ℝ) (u v : ι → ℝ) :
    IntegrableOn (fun t : ℝ => ∑ i ∈ s, ∑ j ∈ s,
      Real.exp (-(a i+a j)*t) * ((a i^2-a j^2)*K i j*u j*v i)) (Ioi (0:ℝ)) := by
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (integrable_sylvester_exponential (a i) (a j) (ha i hi) (ha j hj)).mul_const _

lemma integral_finite_sylvester_commutator
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (K : ι → ι → ℝ) (u v : ι → ℝ) :
    (∫ t : ℝ in Ioi (0:ℝ), ∑ i ∈ s, ∑ j ∈ s,
      Real.exp (-(a i+a j)*t) * ((a i^2-a j^2)*K i j*u j*v i)) =
        ∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*u j*v i := by
  have hint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      IntegrableOn (fun t : ℝ => Real.exp (-(a i+a j)*t) *
        ((a i^2-a j^2)*K i j*u j*v i)) (Ioi (0:ℝ)) :=
    (integrable_sylvester_exponential (a i) (a j) (ha i hi) (ha j hj)).mul_const _
  rw [integral_finsetSum s (fun i hi => integrable_finsetSum s (hint i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (hint i hi)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const, integral_sylvester_exponential (a i) (a j) (ha i hi) (ha j hj)]
  have hab : a i+a j ≠ 0 := ne_of_gt (add_pos (ha i hi) (ha j hj))
  field_simp
  <;> ring

lemma integrable_finite_spectral_square_energy
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) (u : ι → ℝ) :
    IntegrableOn (fun t : ℝ => ∑ i ∈ s, (a i*Real.exp (-a i*t)*u i)^2)
      (Ioi (0:ℝ)) := by
  apply integrable_finsetSum
  intro i hi
  have hf (t : ℝ) : (a i*Real.exp (-a i*t)*u i)^2 =
      Real.exp (-(a i+a i)*t) * (a i^2*u i^2) := by
    rw [show -(a i+a i)*t = -a i*t + -a i*t by ring, Real.exp_add]
    ring
  simp_rw [hf]
  exact (integrable_sylvester_exponential (a i) (a i) (ha i hi) (ha i hi)).mul_const _

lemma integral_finite_spectral_square_energy
    (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) (u : ι → ℝ) :
    (∫ t : ℝ in Ioi (0:ℝ), ∑ i ∈ s, (a i*Real.exp (-a i*t)*u i)^2) =
      (1/2:ℝ) * ∑ i ∈ s, a i*u i^2 := by
  have hint (i : ι) (hi : i ∈ s) :
      IntegrableOn (fun t : ℝ => (a i*Real.exp (-a i*t)*u i)^2) (Ioi (0:ℝ)) := by
    have hf (t : ℝ) : (a i*Real.exp (-a i*t)*u i)^2 =
        Real.exp (-(a i+a i)*t) * (a i^2*u i^2) := by
      rw [show -(a i+a i)*t = -a i*t + -a i*t by ring, Real.exp_add]
      ring
    simp_rw [hf]
    exact (integrable_sylvester_exponential (a i) (a i) (ha i hi) (ha i hi)).mul_const _
  rw [integral_finsetSum s hint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [mul_assoc] using integral_spectral_square_energy_entry (a i) (u i) (ha i hi)

end OAI.AnisotropicCalderon.SpectralSylvester
