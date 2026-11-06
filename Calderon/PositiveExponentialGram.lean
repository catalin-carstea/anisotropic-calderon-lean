import Calderon.SpectralSylvesterIntegral

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace OAI.AnisotropicCalderon.SpectralSylvester

def positiveExponentialVector (r t : ℝ) : ℝ :=
  Real.sqrt 2*r*Real.exp (-(r^2)*t)

lemma integrable_positive_exponential_gram
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => positiveExponentialVector r t*positiveExponentialVector s t)
      (Ioi (0:ℝ)) := by
  have he (t : ℝ) : positiveExponentialVector r t*positiveExponentialVector s t =
      Real.exp (-(r^2+s^2)*t) * (2*r*s) := by
    unfold positiveExponentialVector
    rw [show -(r^2+s^2)*t = -(r^2)*t + -(s^2)*t by ring,Real.exp_add]
    have hh : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      _ = (Real.sqrt 2)^2 *
          (r*s*(Real.exp (-(r^2)*t)*Real.exp (-(s^2)*t))) := by ring
      _ = _ := by rw [hh]; ring
  simp_rw [he]
  exact (integrable_sylvester_exponential (r^2) (s^2) (sq_pos_of_pos hr) (sq_pos_of_pos hs)).mul_const _

lemma integral_positive_exponential_gram
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (∫ t : ℝ in Ioi (0:ℝ), positiveExponentialVector r t*positiveExponentialVector s t) =
      2*r*s/(r^2+s^2) := by
  have he (t : ℝ) : positiveExponentialVector r t*positiveExponentialVector s t =
      Real.exp (-(r^2+s^2)*t) * (2*r*s) := by
    unfold positiveExponentialVector
    rw [show -(r^2+s^2)*t = -(r^2)*t + -(s^2)*t by ring,Real.exp_add]
    have hh : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      _ = (Real.sqrt 2)^2 *
          (r*s*(Real.exp (-(r^2)*t)*Real.exp (-(s^2)*t))) := by ring
      _ = _ := by rw [hh]; ring
  simp_rw [he]
  rw [integral_mul_const,integral_sylvester_exponential (r^2) (s^2)
    (sq_pos_of_pos hr) (sq_pos_of_pos hs)]
  ring

lemma positive_exponential_gram_diagonal (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ in Ioi (0:ℝ), positiveExponentialVector r t*positiveExponentialVector r t) = 1 := by
  rw [integral_positive_exponential_gram r r hr hr]
  have hr0 : r ≠ 0 := ne_of_gt hr
  field_simp
  <;> ring

lemma weighted_midpoint_kernel_identity (r s k : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (2*r*s/(r^2+s^2)) * ((k/(r*s) + r*k/s^3)/2) = k/s^2 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hd : r^2+s^2 ≠ 0 := ne_of_gt (add_pos (sq_pos_of_pos hr) (sq_pos_of_pos hs))
  field_simp
  <;> ring

end OAI.AnisotropicCalderon.SpectralSylvester
