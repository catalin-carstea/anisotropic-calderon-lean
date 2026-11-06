import Calderon.FiniteSpectralSylvester
import Mathlib.Algebra.QuadraticDiscriminant

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace OAI.AnisotropicCalderon.SpectralSylvester

lemma finite_sylvester_quadratic_form_bound
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (K : ι → ι → ℝ) (M : ℝ)
    (hD : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (a i^2-a j^2)*K i j*x j*y i| ≤
        (M/2) * ((∑ i ∈ s, (a i*x i)^2) + ∑ i ∈ s, (a i*y i)^2))
    (u v : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*u j*v i| ≤
      (M/4) * ((∑ i ∈ s, a i*u i^2) + ∑ i ∈ s, a i*v i^2) := by
  let F : ℝ → ℝ := fun t => ∑ i ∈ s, ∑ j ∈ s,
    Real.exp (-(a i+a j)*t) * ((a i^2-a j^2)*K i j*u j*v i)
  let U : ℝ → ℝ := fun t => ∑ i ∈ s, (a i*Real.exp (-a i*t)*u i)^2
  let V : ℝ → ℝ := fun t => ∑ i ∈ s, (a i*Real.exp (-a i*t)*v i)^2
  have hF : IntegrableOn F (Ioi (0:ℝ)) :=
    integrable_finite_sylvester_kernel s a ha K u v
  have hU : IntegrableOn U (Ioi (0:ℝ)) :=
    integrable_finite_spectral_square_energy s a ha u
  have hV : IntegrableOn V (Ioi (0:ℝ)) :=
    integrable_finite_spectral_square_energy s a ha v
  have hpoint (t : ℝ) : |F t| ≤ (M/2) * (U t+V t) := by
    have h := hD (fun i => Real.exp (-a i*t)*u i)
      (fun i => Real.exp (-a i*t)*v i)
    have he : F t = ∑ i ∈ s, ∑ j ∈ s,
        (a i^2-a j^2)*K i j*(Real.exp (-a j*t)*u j)*(Real.exp (-a i*t)*v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [show -(a i+a j)*t = -a i*t + -a j*t by ring, Real.exp_add]
      ring
    rw [he]
    simpa only [U,V,mul_assoc] using h
  have hbound : |∫ t : ℝ in Ioi (0:ℝ), F t| ≤
      ∫ t : ℝ in Ioi (0:ℝ), (M/2)*(U t+V t) :=
    abs_integral_le_integral_abs.trans
      (integral_mono hF.abs ((hU.add hV).const_mul (M/2)) hpoint)
  rw [show (∫ t : ℝ in Ioi (0:ℝ), F t) =
      ∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*u j*v i from
        integral_finite_sylvester_commutator s a ha K u v] at hbound
  rw [integral_const_mul, integral_add hU hV,
    show (∫ t : ℝ in Ioi (0:ℝ), U t) = (1/2:ℝ)*∑ i ∈ s, a i*u i^2 from
      integral_finite_spectral_square_energy s a ha u,
    show (∫ t : ℝ in Ioi (0:ℝ), V t) = (1/2:ℝ)*∑ i ∈ s, a i*v i^2 from
      integral_finite_spectral_square_energy s a ha v] at hbound
  convert hbound using 1 <;> ring

lemma abs_le_half_sqrt_mul_of_quadratic
    (M U V c : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (h : ∀ t : ℝ, t*c ≤ (M/4)*(t^2*U+V)) :
    |c| ≤ (M/2)*Real.sqrt U*Real.sqrt V := by
  have hquad : ∀ t : ℝ, 0 ≤ (M*U)*(t*t)+(-4*c)*t+M*V := by
    intro t
    have ht := h t
    nlinarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hU2 := Real.sq_sqrt hU
  have hV2 := Real.sq_sqrt hV
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have habs : |c|^2 = c^2 := sq_abs c
  have hr : 0 ≤ (M/2)*Real.sqrt U*Real.sqrt V := by positivity
  have hs : ((M/2)*Real.sqrt U*Real.sqrt V)^2 = M^2*U*V/4 := by
    rw [mul_pow,mul_pow,hU2,hV2]
    ring
  nlinarith [sq_nonneg (|c| + (M/2)*Real.sqrt U*Real.sqrt V)]

end OAI.AnisotropicCalderon.SpectralSylvester
