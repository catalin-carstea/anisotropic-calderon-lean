import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace OAI.AnisotropicCalderon.ConnectionError
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_map_le_of_norm_sub_id_le (Q : E →L[ℝ] E) (κ : ℝ)
    (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) (z : E) :
    ‖Q z‖ ≤ (1+κ)*‖z‖ := by
  have h := norm_add_le (Q z-z) z
  simp only [sub_add_cancel] at h
  have h' := h.trans (add_le_add (hQ z) (le_refl ‖z‖))
  convert h' using 1 <;> ring

lemma norm_inverse_apply_le (Q M : E →L[ℝ] E) (κ : ℝ)
    (hκ : κ<1) (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖)
    (hQM : ∀ z, Q (M z)=z) (z : E) : ‖M z‖ ≤ ‖z‖/(1-κ) := by
  have hp : 0<1-κ := by linarith
  have h : ‖M z‖ ≤ ‖z‖+κ*‖M z‖ := by
    calc
      ‖M z‖ = ‖Q (M z)-(Q (M z)-M z)‖ := by congr 1; abel
      _ ≤ ‖Q (M z)‖+‖Q (M z)-M z‖ := norm_sub_le _ _
      _ ≤ ‖z‖+κ*‖M z‖ := by
        have hbound := hQ (M z)
        rw [hQM] at hbound ⊢
        exact add_le_add (le_refl ‖z‖) hbound
  apply (le_div_iff₀ hp).2
  linarith

lemma norm_inverse_apply_le_four_thirds (Q M : E →L[ℝ] E) (κ : ℝ)
    (hκ : κ≤1/4) (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖)
    (hQM : ∀ z, Q (M z)=z) (z : E) : ‖M z‖ ≤ (4/3)*‖z‖ := by
  have hp : 0<1-κ := by linarith
  have h := norm_inverse_apply_le Q M κ (by linarith) hQ hQM z
  have hmul := mul_le_mul_of_nonneg_right hκ (norm_nonneg z)
  apply h.trans
  apply (div_le_iff₀ hp).2
  linarith

theorem inverse_derivative_apply
    (Q M : E → E →L[ℝ] E) (DQ DM : E →L[ℝ] E →L[ℝ] E) (x : E)
    (hQ : HasFDerivAt Q DQ x) (hM : HasFDerivAt M DM x)
    (hQM : (fun y => (Q y).comp (M y)) =ᶠ[𝓝 x] fun _ => ContinuousLinearMap.id ℝ E)
    (hMQ : ∀ z, M x (Q x z)=z) (X Z : E) :
    DM X Z = -M x (DQ X (M x Z)) := by
  have hd := hQ.clm_comp hM
  have hc := hd.congr_of_eventuallyEq hQM.symm
  have hz := hc.unique (hasFDerivAt_const (ContinuousLinearMap.id ℝ E) x)
  have hv := congrArg (fun L => L X Z) hz
  have hsum : Q x (DM X Z)+DQ X (M x Z)=0 := by
    simpa using hv
  have hm := congrArg (M x) hsum
  simp only [map_add,map_zero,hMQ] at hm
  exact eq_neg_of_add_eq_zero_left hm

lemma norm_inverse_derivative_apply_le
    (M : E →L[ℝ] E) (DQ DM : E →L[ℝ] E →L[ℝ] E) (d : ℝ)
    (hd : 0≤d) (hM : ∀ z, ‖M z‖≤(4/3)*‖z‖)
    (hDQ : ∀ X Z, ‖DQ X Z‖≤d*‖X‖*‖Z‖)
    (hDM : ∀ X Z, DM X Z = -M (DQ X (M Z))) (X Z : E) :
    ‖DM X Z‖≤(16/9)*d*‖X‖*‖Z‖ := by
  rw [hDM,norm_neg]
  calc
    ‖M (DQ X (M Z))‖ ≤ (4/3)*‖DQ X (M Z)‖ := hM _
    _ ≤ (4/3)*(d*‖X‖*‖M Z‖) := mul_le_mul_of_nonneg_left (hDQ X (M Z)) (by norm_num)
    _ ≤ (4/3)*(d*‖X‖*((4/3)*‖Z‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM Z) (by positivity)) (by norm_num)
    _ = (16/9)*d*‖X‖*‖Z‖ := by ring

theorem norm_connection_le_of_koszul
    (Q M : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E)
    (T : E → E → E) (q C : ℝ) (hq : 0≤q) (hC : 0≤C)
    (hQ : ∀ z, ‖Q z‖≤q*‖z‖) (hQM : ∀ z, Q (M z)=z)
    (hD : ∀ X Y, ‖D X Y‖≤C*‖X‖*‖Y‖)
    (hT : ∀ X Y Z, 2*inner ℝ (M (T X Y)) Z =
      inner ℝ (D X Y) Z+inner ℝ (D Y X) Z-inner ℝ (D Z X) Y)
    (X Y : E) : ‖T X Y‖≤(3/2)*q*C*‖X‖*‖Y‖ := by
  let Z := M (T X Y)
  have h₁ : |inner ℝ (D X Y) Z|≤C*‖X‖*‖Y‖*‖Z‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hD X Y) (norm_nonneg Z))
  have h₂ : |inner ℝ (D Y X) Z|≤C*‖X‖*‖Y‖*‖Z‖ := by
    have h := (abs_real_inner_le_norm (D Y X) Z).trans
      (mul_le_mul_of_nonneg_right (hD Y X) (norm_nonneg Z))
    convert h using 1 <;> ring
  have h₃ : |inner ℝ (D Z X) Y|≤C*‖X‖*‖Y‖*‖Z‖ := by
    have h := (abs_real_inner_le_norm (D Z X) Y).trans
      (mul_le_mul_of_nonneg_right (hD Z X) (norm_nonneg Y))
    convert h using 1 <;> ring
  have hb : |inner ℝ (D X Y) Z+inner ℝ (D Y X) Z-inner ℝ (D Z X) Y|
      ≤3*C*‖X‖*‖Y‖*‖Z‖ := by
    have h := (abs_add_le (inner ℝ (D X Y) Z+inner ℝ (D Y X) Z)
      (-inner ℝ (D Z X) Y)).trans
      (add_le_add (abs_add_le _ _) (le_refl (|-inner ℝ (D Z X) Y|)))
    simp only [abs_neg] at h
    rw [sub_eq_add_neg]
    linarith
  have hs : 2*‖Z‖^2≤3*C*‖X‖*‖Y‖*‖Z‖ := by
    rw [← hT X Y Z] at hb
    change |2*inner ℝ Z Z|≤_ at hb
    simpa only [real_inner_self_eq_norm_sq,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
      abs_of_nonneg (sq_nonneg ‖Z‖)] using hb
  have hn : ‖Z‖≤(3/2)*C*‖X‖*‖Y‖ := by
    by_cases hz : ‖Z‖=0
    · rw [hz]; positivity
    · have hp : 0<‖Z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hm : (2*‖Z‖)*‖Z‖≤(3*C*‖X‖*‖Y‖)*‖Z‖ := by convert hs using 1 <;> ring
      have h := le_of_mul_le_mul_right hm hp
      linarith
  have hnorm := hQ Z
  have hident : Q Z=T X Y := hQM _
  rw [hident] at hnorm
  have h := hnorm.trans (mul_le_mul_of_nonneg_left hn hq)
  convert h using 1 <;> ring

#print axioms inverse_derivative_apply
#print axioms norm_connection_le_of_koszul
end OAI.AnisotropicCalderon.ConnectionError
