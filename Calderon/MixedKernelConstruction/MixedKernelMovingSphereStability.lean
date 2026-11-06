import Calderon.MixedKernelConstruction.MixedKernelMovingSphereLeading
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- Squared distances have the exact one-sided first-order perturbation bound. -/
theorem norm_sub_square_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x e : E) :
    ‖x‖^2-2*‖x‖*‖e‖ ≤ ‖x-e‖^2 := by
  rw [norm_sub_sq_real]
  nlinarith [real_inner_le_norm x e,sq_nonneg ‖e‖]

/-- A bounded reference vector controls the quadratic perturbation of a linear functional. -/
theorem inner_square_perturbation_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b z0 z : E) (hz0 : ‖z0‖ ≤ 2) :
    ⟪b,z⟫_ℝ^2 ≤ ⟪b,z0⟫_ℝ^2+4*‖b‖^2*‖z-z0‖+‖b‖^2*‖z-z0‖^2 := by
  let a := ⟪b,z0⟫_ℝ
  let u := ⟪b,z-z0⟫_ℝ
  have ha : |a| ≤ 2*‖b‖ :=
    (abs_real_inner_le_norm b z0).trans (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz0 (norm_nonneg b))
  have hu : |u| ≤ ‖b‖*‖z-z0‖ := abs_real_inner_le_norm _ _
  have hcross : a*u ≤ 2*‖b‖^2*‖z-z0‖ := by
    calc a*u ≤ |a*u| := le_abs_self _
      _ = |a| * |u| := abs_mul _ _
      _ ≤ (2*‖b‖)*(‖b‖*‖z-z0‖) := mul_le_mul ha hu (abs_nonneg _) (by positivity)
      _ = 2*‖b‖^2*‖z-z0‖ := by ring
  have husq : u^2 ≤ ‖b‖^2*‖z-z0‖^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg u) (mul_nonneg (norm_nonneg b) (norm_nonneg (z-z0)))).mpr hu
    simpa only [sq_abs,mul_pow] using hh
  have heq : ⟪b,z⟫_ℝ = a+u := by dsimp only [a,u]; rw [inner_sub_right]; ring
  rw [heq]
  nlinarith [hcross,husq]

/-- Positive leading energy absorbs its square-root error, retaining the necessary B*d order. -/
theorem leading_form_error_absorption (B d t E E' : ℝ)
    (hB : 0 ≤ B) (hd : 0 ≤ d) (ht : 0 ≤ t) (hE : 0 ≤ E)
    (htsq : t^2 ≤ E+16*B^2)
    (hperturb : E-6*B*d-2*t*d-d^2/8 ≤ E') :
    -16*(B*d+d^2) ≤ E' := by
  let s := Real.sqrt E
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = E := Real.sq_sqrt hE
  have hts : t ≤ s+4*B := by
    have hsqle : t^2 ≤ (s+4*B)^2 := by nlinarith [mul_nonneg hs0 hB]
    exact (sq_le_sq₀ ht (by positivity)).mp hsqle
  have htd := mul_le_mul_of_nonneg_right hts hd
  nlinarith [sq_nonneg (s-d),mul_nonneg hB hd,sq_nonneg d]

/-- Full vector stability of a nonnegative leading form under arbitrary endpoint perturbations.
The explicit reference bounds are subsequently discharged for the normalized sphere vectors. -/
theorem moving_sphere_leading_form_stability_of_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega v b q0 w0 q w : E) (d : ℝ)
    (hb : ‖b‖ ≤ 1/4) (hq0 : ‖q0‖ ≤ 2) (hw0 : ‖w0‖ ≤ 2)
    (homegaq0 : ‖omega-q0‖ ≤ 2*‖b‖) (hd : ‖q-q0‖+‖w-w0‖ ≤ d)
    (hE : 0 ≤ ‖omega-q0‖^2+‖v-w0‖^2-2*(⟪b,q0⟫_ℝ^2+⟪b,w0⟫_ℝ^2)) :
    -16*(‖b‖*d+d^2) ≤ ‖omega-q‖^2+‖v-w‖^2-2*(⟪b,q⟫_ℝ^2+⟪b,w⟫_ℝ^2) := by
  let B := ‖b‖
  let e := ‖q-q0‖
  let f := ‖w-w0‖
  let t := ‖v-w0‖
  let E0 := ‖omega-q0‖^2+t^2-2*(⟪b,q0⟫_ℝ^2+⟪b,w0⟫_ℝ^2)
  have hB0 : 0 ≤ B := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  have hf0 : 0 ≤ f := norm_nonneg _
  have ht0 : 0 ≤ t := norm_nonneg _
  have hd0 : 0 ≤ d := by change e+f ≤ d at hd; linarith only [hd,he0,hf0]
  have hefd : e+f ≤ d := hd
  have hed : e ≤ d := by linarith only [hefd,hf0]
  have hfd : f ≤ d := by linarith only [hefd,he0]
  have hef2 : e^2+f^2 ≤ d^2 := by
    have hsum := (sq_le_sq₀ (add_nonneg he0 hf0) hd0).mpr hefd
    nlinarith only [hsum,mul_nonneg he0 hf0]
  have hq0i : |⟪b,q0⟫_ℝ| ≤ 2*B :=
    (abs_real_inner_le_norm b q0).trans (by
      simpa only [B,mul_comm] using mul_le_mul_of_nonneg_left hq0 (norm_nonneg b))
  have hw0i : |⟪b,w0⟫_ℝ| ≤ 2*B :=
    (abs_real_inner_le_norm b w0).trans (by
      simpa only [B,mul_comm] using mul_le_mul_of_nonneg_left hw0 (norm_nonneg b))
  have hq0sq : ⟪b,q0⟫_ℝ^2 ≤ 4*B^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg ⟪b,q0⟫_ℝ) (by positivity : 0 ≤ 2*B)).mpr hq0i
    nlinarith only [hh,sq_abs ⟪b,q0⟫_ℝ]
  have hw0sq : ⟪b,w0⟫_ℝ^2 ≤ 4*B^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg ⟪b,w0⟫_ℝ) (by positivity : 0 ≤ 2*B)).mpr hw0i
    nlinarith only [hh,sq_abs ⟪b,w0⟫_ℝ]
  have htsq : t^2 ≤ E0+16*B^2 := by dsimp only [E0]; nlinarith only [hq0sq,hw0sq,sq_nonneg ‖omega-q0‖]
  have hqnorm : ‖omega-q0‖^2-4*B*e ≤ ‖omega-q‖^2 := by
    have hh := norm_sub_square_lower (omega-q0) (q-q0)
    have heq : omega-q0-(q-q0) = omega-q := by abel
    rw [heq] at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_right homegaq0 he0]
  have hwnorm : t^2-2*t*f ≤ ‖v-w‖^2 := by
    have hh := norm_sub_square_lower (v-w0) (w-w0)
    have heq : v-w0-(w-w0) = v-w := by abel
    rw [heq] at hh
    exact hh
  have hqpert := inner_square_perturbation_bound b q0 q hq0
  have hwpert := inner_square_perturbation_bound b w0 w hw0
  have hBsmall : B ≤ 1/4 := hb
  have hBsq : B^2 ≤ B/4 := by nlinarith only [mul_nonneg hB0 (sub_nonneg.mpr hBsmall)]
  have hBsq' : B^2 ≤ 1/16 := by nlinarith only [hBsq,hBsmall]
  have heterm : 4*B*e ≤ 4*B*d := mul_le_mul_of_nonneg_left hed (by positivity)
  have hfterm : 2*t*f ≤ 2*t*d := mul_le_mul_of_nonneg_left hfd (by positivity)
  have hlin : 8*B^2*(e+f) ≤ 2*B*d := by
    calc 8*B^2*(e+f) ≤ 8*B^2*d := mul_le_mul_of_nonneg_left hefd (by positivity)
      _ ≤ 2*B*d := by nlinarith only [mul_le_mul_of_nonneg_right hBsq hd0]
  have hquad : 2*B^2*(e^2+f^2) ≤ d^2/8 := by
    calc 2*B^2*(e^2+f^2) ≤ 2*B^2*d^2 := mul_le_mul_of_nonneg_left hef2 (by positivity)
      _ ≤ d^2/8 := by nlinarith only [mul_le_mul_of_nonneg_right hBsq' (sq_nonneg d)]
  apply leading_form_error_absorption B d t E0 _ hB0 hd0 ht0 hE htsq
  change ⟪b,q⟫_ℝ^2 ≤ ⟪b,q0⟫_ℝ^2+4*B^2*e+B^2*e^2 at hqpert
  change ⟪b,w⟫_ℝ^2 ≤ ⟪b,w0⟫_ℝ^2+4*B^2*f+B^2*f^2 at hwpert
  dsimp only [E0]
  nlinarith only [hqnorm,hwnorm,hqpert,hwpert,heterm,hfterm,hlin,hquad]

/-- The exact inverted normal has uniform size and displacement at small radius gradient. -/
theorem normalized_sum_reference_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega b q : E) (homega : ‖omega‖ = 1) (hb : ‖b‖ ≤ 1/4)
    (hn : omega+b ≠ 0) (hq : q = (‖omega+b‖^2)⁻¹ • (omega+b)) :
    ‖q‖ ≤ 2 ∧ ‖omega-q‖ ≤ 2*‖b‖ := by
  have hNpos : 0 < ‖omega+b‖ := norm_pos_iff.mpr hn
  have hN : (1/2 : ℝ) ≤ ‖omega+b‖ := by
    have hh := norm_sub_norm_le omega (-b)
    simp only [homega,norm_neg,sub_neg_eq_add] at hh
    linarith
  have hN2 : (1/4 : ℝ) ≤ ‖omega+b‖^2 := by nlinarith
  have hC : 0 < ‖omega+b‖^2 := sq_pos_of_pos hNpos
  have hqnorm : ‖q‖ = ‖omega+b‖⁻¹ := by
    rw [hq,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hC)]
    field_simp [hNpos.ne'] <;> ring
  have hqbound : ‖q‖ ≤ 2 := by
    rw [hqnorm,inv_eq_one_div]
    exact (div_le_iff₀ hNpos).mpr (by linarith)
  have hscale : ‖omega+b‖^2 • q = omega+b := by
    rw [hq,smul_smul,mul_inv_cancel₀ hC.ne',one_smul]
  have hnq : ⟪omega+b,q⟫_ℝ = 1 := by
    rw [hq,real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact inv_mul_cancel₀ hC.ne'
  have hCC : ‖omega+b‖^2*‖q‖^2 = 1 := by
    have hh : ⟪‖omega+b‖^2 • q,q⟫_ℝ = 1 := by rw [hscale]; exact hnq
    simpa only [real_inner_smul_left,real_inner_self_eq_norm_sq] using hh
  have hAC : ‖omega+b‖^2*⟪omega,q⟫_ℝ = ⟪omega,omega+b⟫_ℝ := by
    calc ‖omega+b‖^2*⟪omega,q⟫_ℝ = ⟪omega,‖omega+b‖^2 • q⟫_ℝ := by rw [real_inner_smul_right]
      _ = ⟪omega,omega+b⟫_ℝ := by rw [hscale]
  have hoo : ⟪omega,omega⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,homega]; norm_num
  have hNorm : ‖omega+b‖^2 = 1+2*⟪omega,b⟫_ℝ+‖b‖^2 := by
    rw [norm_add_sq_real,homega]
    norm_num
  have hinner : ⟪omega,omega+b⟫_ℝ = 1+⟪omega,b⟫_ℝ := by rw [inner_add_right,hoo]
  have hInv : ‖omega-q‖^2*‖omega+b‖^2 = ‖b‖^2 := by
    rw [norm_sub_sq_real,homega]
    nlinarith [hCC,hAC,hNorm,hinner]
  have hm := mul_le_mul_of_nonneg_left hN2 (sq_nonneg ‖omega-q‖)
  have hdist : ‖omega-q‖ ≤ 2*‖b‖ :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by nlinarith [hInv,hm])
  exact ⟨hqbound,hdist⟩

/-- Exact normalized moving-sphere vectors have arbitrary small metric-normalization errors
with the necessary quadratic/mixed error bound and no extra original premise. -/
theorem moving_sphere_leading_form_stability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (omega v b q0 w0 q w : E) (d : ℝ)
    (homega : ‖omega‖ = 1) (hv : ‖v‖ = 1) (hov : ⟪omega,v⟫_ℝ = 0)
    (hb : ‖b‖ ≤ 1/4) (hn : omega+b ≠ 0)
    (hq0 : q0 = (‖omega+b‖^2)⁻¹ • (omega+b))
    (hnw0 : ⟪omega+b,w0⟫_ℝ = 0) (hww0 : ‖w0‖^2 = ‖q0‖^2)
    (hd : ‖q-q0‖+‖w-w0‖ ≤ d) :
    -16*(‖b‖*d+d^2) ≤ ‖omega-q‖^2+‖v-w‖^2-2*(⟪b,q⟫_ℝ^2+⟪b,w⟫_ℝ^2) := by
  obtain ⟨hqn,hqdist⟩ := normalized_sum_reference_bounds omega b q0 homega hb hn hq0
  have hwn : ‖w0‖ ≤ 2 := by nlinarith [hww0,norm_nonneg w0,norm_nonneg q0]
  have hE := moving_sphere_leading_form_nonneg omega v b q0 w0 homega hv hov
    (show ‖b‖ ≤ 1 by linarith) hn hq0 hnw0 hww0
  exact moving_sphere_leading_form_stability_of_bounds omega v b q0 w0 q w d hb hqn hwn hqdist hd hE

/-- A small squared-length normalization error admits an exactly normalized, orthogonal,
nearby comparison vector, with the quantitative linear error required for metric perturbations. -/
theorem exists_normalized_orthogonal_near
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n w : E) (c eta : ℝ) (hc : (1/2 : ℝ) ≤ c) (heta : 0 ≤ eta) (heta1 : eta ≤ 1/8)
    (horth : ⟪n,w⟫_ℝ = 0) (hnorm : |‖w‖^2-c^2| ≤ eta) :
    ∃ w0 : E, ⟪n,w0⟫_ℝ = 0 ∧ ‖w0‖ = c ∧ ‖w-w0‖ ≤ 2*eta := by
  have hc0 : 0 < c := by linarith
  have hwpos : 0 < ‖w‖ := by
    by_contra h
    have hzero : ‖w‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hzero] at hnorm
    have ha := (abs_le.mp hnorm).1
    nlinarith
  let w0 := (c/‖w‖) • w
  have hscale : (1-c/‖w‖)*‖w‖ = ‖w‖-c := by field_simp [hwpos.ne'] <;> ring
  have hdist : ‖w-w0‖ = |‖w‖-c| := by
    have he : w-w0 = (1-c/‖w‖) • w := by dsimp only [w0]; rw [sub_smul,one_smul]
    rw [he,norm_smul,Real.norm_eq_abs]
    calc |1-c/‖w‖| *‖w‖ = |1-c/‖w‖| * |‖w‖| := by rw [abs_of_pos hwpos]
      _ = |(1-c/‖w‖)*‖w‖| := (abs_mul _ _).symm
      _ = |‖w‖-c| := congrArg abs hscale
  have habs : |‖w‖^2-c^2| = |‖w‖-c| *(‖w‖+c) := by
    rw [show ‖w‖^2-c^2 = (‖w‖-c)*(‖w‖+c) by ring,abs_mul,
      abs_of_pos (by positivity : 0 < ‖w‖+c)]
  have hclose : |‖w‖-c| ≤ 2*eta := by
    rw [habs] at hnorm
    have hh := mul_le_mul_of_nonneg_left
      (show (1/2 : ℝ) ≤ ‖w‖+c by linarith [norm_nonneg w]) (abs_nonneg (‖w‖-c))
    nlinarith
  refine ⟨w0,?_,?_,?_⟩
  · dsimp only [w0]
    rw [real_inner_smul_right,horth,mul_zero]
  · dsimp only [w0]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hc0 hwpos)]
    exact div_mul_cancel₀ _ hwpos.ne'
  · rw [hdist]
    exact hclose

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
