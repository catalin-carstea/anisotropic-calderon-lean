import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

namespace OAI.AnisotropicCalderon.RadiusProfile

noncomputable def softplus (δ t : ℝ) : ℝ := δ * Real.log (1 + Real.exp (t/δ))

noncomputable def logSlope (δ t : ℝ) : ℝ :=
  Real.exp (t/δ) / (δ * (1+Real.exp (t/δ)) * Real.log (1+Real.exp (t/δ)))

noncomputable def logSlopeDerivative (δ t : ℝ) : ℝ :=
  Real.exp (t/δ) * (Real.log (1+Real.exp (t/δ))-Real.exp (t/δ)) /
    (δ^2 * (1+Real.exp (t/δ))^2 * (Real.log (1+Real.exp (t/δ)))^2)

lemma log_exp_add_one_pos (s : ℝ) : 0 < Real.log (1+Real.exp s) := by
  apply Real.log_pos
  linarith [Real.exp_pos s]

lemma softplus_pos (δ t : ℝ) (hδ : 0 < δ) : 0 < softplus δ t :=
  mul_pos hδ (log_exp_add_one_pos (t/δ))

theorem hasDerivAt_softplus (δ t : ℝ) (hδ : δ ≠ 0) :
    HasDerivAt (softplus δ) (Real.exp (t/δ)/(1+Real.exp (t/δ))) t := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (u/δ)) (Real.exp (t/δ)/δ) t := by
    simpa only [id_eq,div_eq_mul_inv,one_mul] using ((hasDerivAt_id' t).div_const δ).exp
  have hs : HasDerivAt (fun u : ℝ => 1+Real.exp (u/δ)) (Real.exp (t/δ)/δ) t := by
    convert! (hasDerivAt_const t (1:ℝ)).add he using 1 <;> simp only [Pi.add_apply,zero_add]
  have hlog := hs.log (by positivity)
  have h := hlog.const_mul δ
  convert h using 1
  · rfl
  · field_simp [hδ]

lemma softplus_derivative_pos (δ t : ℝ) : 0 < Real.exp (t/δ)/(1+Real.exp (t/δ)) := by
  positivity

lemma softplus_derivative_lt_one (δ t : ℝ) : Real.exp (t/δ)/(1+Real.exp (t/δ)) < 1 := by
  apply (div_lt_one (by positivity)).2
  linarith

lemma logSlope_pos (δ t : ℝ) (hδ : 0 < δ) : 0 < logSlope δ t := by
  unfold logSlope
  exact div_pos (Real.exp_pos _) (by positivity [log_exp_add_one_pos (t/δ)])

theorem hasDerivAt_log_softplus (δ t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun u => Real.log (softplus δ u)) (logSlope δ t) t := by
  have h := (hasDerivAt_softplus δ t (ne_of_gt hδ)).log (ne_of_gt (softplus_pos δ t hδ))
  convert h using 1
  unfold softplus logSlope
  field_simp

theorem hasDerivAt_logSlope (δ t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (logSlope δ) (logSlopeDerivative δ t) t := by
  have hLp := log_exp_add_one_pos (t/δ)
  have he : HasDerivAt (fun u : ℝ => Real.exp (u/δ)) (Real.exp (t/δ)/δ) t := by
    simpa only [id_eq,div_eq_mul_inv,one_mul] using ((hasDerivAt_id' t).div_const δ).exp
  have hs : HasDerivAt (fun u : ℝ => 1+Real.exp (u/δ)) (Real.exp (t/δ)/δ) t := by
    convert! (hasDerivAt_const t (1:ℝ)).add he using 1 <;> simp only [Pi.add_apply,zero_add]
  have hL := hs.log (by positivity)
  have hden : HasDerivAt
      (fun u : ℝ => δ*(1+Real.exp (u/δ))*Real.log (1+Real.exp (u/δ)))
      (δ*(Real.exp (t/δ)/δ)*Real.log (1+Real.exp (t/δ))+
        δ*(1+Real.exp (t/δ))*((Real.exp (t/δ)/δ)/(1+Real.exp (t/δ)))) t := by
    convert! (hs.const_mul δ).mul hL using 1 <;> simp only [Pi.mul_apply]
  have h := he.div hden (by positivity)
  convert h using 1
  · rfl
  · unfold logSlopeDerivative
    field_simp [ne_of_gt hδ,ne_of_gt hLp]
    <;> ring

lemma logSlopeDerivative_neg (δ t : ℝ) (hδ : 0 < δ) : logSlopeDerivative δ t < 0 := by
  have he : 0 < Real.exp (t/δ) := Real.exp_pos _
  have hL : Real.log (1+Real.exp (t/δ)) < Real.exp (t/δ) := by
    have h := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1+Real.exp (t/δ))
      (by linarith : 1+Real.exp (t/δ) ≠ 1)
    linarith
  unfold logSlopeDerivative
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg he (sub_neg.mpr hL))
    (by positivity [log_exp_add_one_pos (t/δ)])

lemma logSlope_mul_softplus (δ t : ℝ) (hδ : 0 < δ) :
    logSlope δ t * softplus δ t = Real.exp (t/δ)/(1+Real.exp (t/δ)) := by
  have hL : Real.log (1+Real.exp (t/δ)) ≠ 0 := ne_of_gt (log_exp_add_one_pos _)
  unfold logSlope softplus
  field_simp

lemma logSlope_le_inv_softplus (δ t : ℝ) (hδ : 0 < δ) :
    logSlope δ t ≤ 1 / softplus δ t := by
  apply (le_div_iff₀ (softplus_pos δ t hδ)).2
  rw [logSlope_mul_softplus δ t hδ]
  exact le_of_lt (softplus_derivative_lt_one δ t)

lemma le_softplus (δ t : ℝ) (hδ : 0 < δ) : t ≤ softplus δ t := by
  have h := Real.log_le_log (Real.exp_pos (t/δ))
    (by linarith : Real.exp (t/δ) ≤ 1+Real.exp (t/δ))
  rw [Real.log_exp] at h
  have hm := mul_le_mul_of_nonneg_left h (le_of_lt hδ)
  unfold softplus
  have hi : δ * (t/δ) = t := by field_simp
  simpa only [hi] using hm

lemma softplus_le_delta_log_two (δ t : ℝ) (hδ : 0 < δ) (ht : t ≤ 0) :
    softplus δ t ≤ δ * Real.log 2 := by
  have he : Real.exp (t/δ) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (div_nonpos_of_nonpos_of_nonneg ht (le_of_lt hδ))
  have h := Real.log_le_log (by positivity : 0 < 1+Real.exp (t/δ))
    (by linarith : 1+Real.exp (t/δ) ≤ 2)
  exact mul_le_mul_of_nonneg_left h (le_of_lt hδ)

#print axioms hasDerivAt_softplus
#print axioms hasDerivAt_logSlope
#print axioms logSlopeDerivative_neg
end OAI.AnisotropicCalderon.RadiusProfile
