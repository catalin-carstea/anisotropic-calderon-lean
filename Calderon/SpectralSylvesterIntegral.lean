import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact scalar entries behind the finite spectral Sylvester formula.
No actual Dirichlet-to-Neumann commutator estimate is assumed or proved here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace OAI.AnisotropicCalderon.SpectralSylvester

lemma sylvester_commutator_entry (a b k : ℝ) :
    (a+b)*((a-b)*k) = (a^2-b^2)*k := by ring

lemma integrable_sylvester_exponential (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a+b)*t)) (Ioi (0:ℝ)) :=
  integrableOn_exp_mul_Ioi (by linarith : -(a+b) < 0) 0

lemma integral_sylvester_exponential (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in Ioi (0:ℝ), Real.exp (-(a+b)*t)) = (a+b)⁻¹ := by
  rw [integral_exp_mul_Ioi (by linarith : -(a+b) < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

lemma integral_sylvester_commutator_entry
    (a b k u v : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in Ioi (0:ℝ),
      Real.exp (-a*t) * ((a^2-b^2)*k*u*v) * Real.exp (-b*t)) =
        (a-b)*k*u*v := by
  have hf (t : ℝ) :
      Real.exp (-a*t) * ((a^2-b^2)*k*u*v) * Real.exp (-b*t) =
        Real.exp (-(a+b)*t) * ((a^2-b^2)*k*u*v) := by
    rw [show -(a+b)*t = -a*t + -b*t by ring, Real.exp_add]
    ring
  simp_rw [hf]
  rw [integral_mul_const, integral_sylvester_exponential a b ha hb]
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  field_simp
  <;> ring

lemma integral_spectral_square_energy_entry (a u : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi (0:ℝ), (a * Real.exp (-a*t) * u)^2) =
      (1/2:ℝ) * a * u^2 := by
  have hf (t : ℝ) : (a * Real.exp (-a*t) * u)^2 =
      Real.exp (-(a+a)*t) * (a^2*u^2) := by
    rw [show -(a+a)*t = -a*t + -a*t by ring, Real.exp_add]
    ring
  simp_rw [hf]
  rw [integral_mul_const, integral_sylvester_exponential a a ha ha]
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp
  <;> ring

end OAI.AnisotropicCalderon.SpectralSylvester
