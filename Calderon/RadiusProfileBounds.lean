import Calderon.RadiusProfile
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI.AnisotropicCalderon.RadiusProfile

noncomputable def deltaDerivative (t δ : ℝ) : ℝ :=
  Real.log (1+Real.exp (t/δ))-(t/δ)*Real.exp (t/δ)/(1+Real.exp (t/δ))

theorem hasDerivAt_softplus_delta (t δ : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun a => softplus a t) (deltaDerivative t δ) δ := by
  have hratio : HasDerivAt (fun a : ℝ => t/a) (-t/δ^2) δ := by
    convert! (hasDerivAt_const δ t).div (hasDerivAt_id δ) (ne_of_gt hδ) using 1
    <;> simp
  have he := hratio.exp
  have hs : HasDerivAt (fun a : ℝ => 1+Real.exp (t/a))
      (Real.exp (t/δ)*(-t/δ^2)) δ := by
    convert! (hasDerivAt_const δ (1:ℝ)).add he using 1 <;> simp
  have hL := hs.log (by positivity)
  have h := (hasDerivAt_id δ).mul hL
  convert! h using 1
  unfold deltaDerivative
  dsimp only [id_eq]
  field_simp [ne_of_gt hδ]
  <;> ring

lemma deltaDerivative_pos (t δ : ℝ) : 0 < deltaDerivative t δ := by
  have hL := log_exp_add_one_pos (t/δ)
  unfold deltaDerivative
  by_cases hs : 0≤t/δ
  · have hLs : t/δ < Real.log (1+Real.exp (t/δ)) := by
      have h := Real.log_lt_log (Real.exp_pos (t/δ))
        (by linarith : Real.exp (t/δ)<1+Real.exp (t/δ))
      simpa only [Real.log_exp] using h
    have hfrac : (t/δ)*Real.exp (t/δ)/(1+Real.exp (t/δ)) ≤ t/δ := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    linarith
  · have hs' : t/δ≤0 := le_of_not_ge hs
    have hfrac : (t/δ)*Real.exp (t/δ)/(1+Real.exp (t/δ))≤0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hs' (le_of_lt (Real.exp_pos _))) (by positivity)
    linarith

theorem strictMono_softplus (δ : ℝ) (hδ : 0 < δ) : StrictMono (softplus δ) :=
  strictMono_of_hasDerivAt_pos (fun t => hasDerivAt_softplus δ t (ne_of_gt hδ))
    (fun t => softplus_derivative_pos δ t)

theorem strictMonoOn_softplus_delta (t : ℝ) :
    StrictMonoOn (fun δ => softplus δ t) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0:ℝ))
  · intro δ hδ
    exact (hasDerivAt_softplus_delta t δ hδ).continuousAt.continuousWithinAt
  · intro δ hδ
    have hd : 0 < δ := interior_subset hδ
    rw [(hasDerivAt_softplus_delta t δ hd).deriv]
    exact deltaDerivative_pos t δ

lemma softplus_le_unit (δ t : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    softplus δ t ≤ softplus 1 t :=
  (strictMonoOn_softplus_delta t).monotoneOn hδ (by norm_num) hδ₁

lemma softplus_le_log_exp_upper (δ t T : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ht : t ≤ T) :
    softplus δ t ≤ Real.log (1+Real.exp T) := by
  have h := (softplus_le_unit δ t hδ hδ₁).trans
    ((strictMono_softplus 1 (by norm_num)).monotone ht)
  simpa only [softplus,div_one,one_mul] using h

lemma softplus_small_of_nonpos (δ t ε : ℝ) (hδ : 0 < δ) (ht : t ≤ 0)
    (hsmall : δ ≤ ε / Real.log 2) : softplus δ t ≤ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (softplus_le_delta_log_two δ t hδ ht).trans ((le_div_iff₀ hlog).mp hsmall)

theorem radius_gradient_scale_bound (δ t R C b : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hp : 2 ≤ p) (hbound : b ≤ (p:ℝ)*C*logSlope δ t) :
    (R*(softplus δ t)^p)*b^2 ≤ R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2) := by
  have hℓ := softplus_pos δ t hδ
  have ha := logSlope_pos δ t hδ
  have hsq : b^2 ≤ ((p:ℝ)*C*logSlope δ t)^2 := by
    nlinarith
  have hm : 0≤logSlope δ t*softplus δ t := by positivity
  have hm₁ : logSlope δ t*softplus δ t≤1 := by
    rw [logSlope_mul_softplus δ t hδ]
    exact le_of_lt (softplus_derivative_lt_one δ t)
  have hsq₁ : (logSlope δ t*softplus δ t)^2≤1 := by nlinarith
  have hpow : (softplus δ t)^p = (softplus δ t)^(p-2)*(softplus δ t)^2 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (R*(softplus δ t)^p)*b^2 ≤ (R*(softplus δ t)^p)*((p:ℝ)*C*logSlope δ t)^2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2))*(logSlope δ t*softplus δ t)^2 := by
      rw [hpow]
      ring
    _ ≤ (R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2))*1 :=
      mul_le_mul_of_nonneg_left hsq₁ (by positivity)
    _ = R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2) := mul_one _

theorem radius_gradient_uniform_scale_bound (δ t T R C b : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ht : t ≤ T)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hp : 2 ≤ p) (hbound : b ≤ (p:ℝ)*C*logSlope δ t) :
    (R*(softplus δ t)^p)*b^2 ≤ R*(p:ℝ)^2*C^2*(Real.log (1+Real.exp T))^(p-2) := by
  have hbase := radius_gradient_scale_bound δ t R C b p hδ hR hC hb hp hbound
  have hpow := pow_le_pow_left₀ (le_of_lt (softplus_pos δ t hδ))
    (softplus_le_log_exp_upper δ t T hδ hδ₁ ht) (p-2)
  exact hbase.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

noncomputable def profileHessianForm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (δ t : ℝ) (p : ℕ) (H : E → E → ℝ) (ell : E →L[ℝ] ℝ)
    (X Y : E) : ℝ :=
  (p:ℝ)*logSlope δ t*H X Y+(p:ℝ)*logSlopeDerivative δ t*(ell X)*(ell Y)

theorem profileHessianForm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ t c C : ℝ) (p : ℕ) (H : E → E → ℝ) (ell : E →L[ℝ] ℝ)
    (hδ : 0 < δ) (hc : 0 ≤ c) (hC : 0 < C) (hell : ‖ell‖≤C)
    (hH : ∀ X, H X X≤-c*‖X‖^2) (X : E) :
    profileHessianForm δ t p H ell X X ≤
      -(c/C)*((p:ℝ)*logSlope δ t*‖ell‖)*‖X‖^2 := by
  have ha := logSlope_pos δ t hδ
  have ha' := logSlopeDerivative_neg δ t hδ
  have hfirst := mul_le_mul_of_nonneg_left (hH X)
    (show 0≤(p:ℝ)*logSlope δ t by positivity)
  have hsecond : (p:ℝ)*logSlopeDerivative δ t*(ell X)*(ell X)≤0 := by
    have h := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p) (le_of_lt ha')) (sq_nonneg (ell X))
    convert h using 1 <;> ring
  have hform : profileHessianForm δ t p H ell X X≤-((p:ℝ)*logSlope δ t*c)*‖X‖^2 := by
    unfold profileHessianForm
    nlinarith
  have hgrad := mul_le_mul_of_nonneg_left hell
    (show 0≤(p:ℝ)*logSlope δ t by positivity)
  have hgrad' := mul_le_mul_of_nonneg_left hgrad (show 0≤c/C by positivity)
  have heq : (c/C)*((p:ℝ)*logSlope δ t*C) = (p:ℝ)*logSlope δ t*c := by
    field_simp
  rw [heq] at hgrad'
  have hneg := neg_le_neg (mul_le_mul_of_nonneg_right hgrad' (sq_nonneg ‖X‖))
  apply hform.trans
  convert hneg using 1 <;> ring

#print axioms hasDerivAt_softplus_delta
#print axioms strictMonoOn_softplus_delta
#print axioms radius_gradient_scale_bound
#print axioms radius_gradient_uniform_scale_bound
#print axioms profileHessianForm_le
end OAI.AnisotropicCalderon.RadiusProfile
