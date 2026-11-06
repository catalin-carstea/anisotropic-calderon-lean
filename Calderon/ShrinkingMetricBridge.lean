import Calderon.ShrinkingPerturbation
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open OAI.AnisotropicCalderon
namespace OAI.AnisotropicCalderon.ShrinkingMetricBridge

open ShrinkingGeometry ShrinkingPerturbation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_map_sub_le_of_opNorm (Q : E →L[ℝ] E) (κ : ℝ)
    (hQ : ‖Q-ContinuousLinearMap.id ℝ E‖ ≤ κ) (z : E) :
    ‖Q z-z‖ ≤ κ*‖z‖ := by
  have h := (Q-ContinuousLinearMap.id ℝ E).le_opNorm z
  have hκ := mul_le_mul_of_nonneg_right hQ (norm_nonneg z)
  simpa only [sub_apply,ContinuousLinearMap.id_apply] using h.trans hκ

lemma abs_quadratic_form_sub_norm_sq_le (Q : E →L[ℝ] E) (κ : ℝ)
    (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) (z : E) :
    |inner ℝ z (Q z)-‖z‖^2| ≤ κ*‖z‖^2 := by
  have hid : inner ℝ z (Q z)-‖z‖^2 = inner ℝ z (Q z-z) := by
    rw [inner_sub_right,real_inner_self_eq_norm_sq]
  rw [hid]
  have h := (abs_real_inner_le_norm z (Q z-z)).trans
    (mul_le_mul_of_nonneg_left (hQ z) (norm_nonneg z))
  convert h using 1 <;> ring

lemma quadratic_form_bounds (Q : E →L[ℝ] E) (κ : ℝ)
    (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) (z : E) :
    (1-κ)*‖z‖^2 ≤ inner ℝ z (Q z) ∧
      inner ℝ z (Q z) ≤ (1+κ)*‖z‖^2 := by
  have h := abs_quadratic_form_sub_norm_sq_le Q κ hQ z
  obtain ⟨h₁,h₂⟩ := abs_le.mp h
  constructor <;> linarith

lemma norm_normalized_map_sub_le (Q : E →L[ℝ] E) (u : E) (κ : ℝ)
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1/4) (hs : 3/4 ≤ ‖u‖)
    (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) :
    ‖(1 / inner ℝ u (Q u)) • Q u-(1 / ‖u‖^2) • u‖ ≤ 4*κ := by
  let t : ℝ := inner ℝ u (Q u)
  have hform := abs_quadratic_form_sub_norm_sq_le Q κ hQ u
  have htlo := (quadratic_form_bounds Q κ hQ u).1
  have hmulκ := mul_le_mul_of_nonneg_right hκ₁ (sq_nonneg ‖u‖)
  have hmulnorm := mul_le_mul_of_nonneg_right hs (norm_nonneg u)
  have hspos : 0 < ‖u‖ := by linarith
  have htge : ‖u‖/2 ≤ t := by dsimp [t]; linarith only [htlo,hmulκ,hmulnorm,hs]
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hsne : ‖u‖ ≠ 0 := ne_of_gt hspos
  have hrecip : |1/t-1/‖u‖^2| = |t-‖u‖^2|/(t*‖u‖^2) := by
    have hid : 1/t-1/‖u‖^2 = -(t-‖u‖^2)/(t*‖u‖^2) := by
      field_simp [htne,hsne]
      ring
    rw [hid,abs_div,abs_neg,abs_of_nonneg (show 0 ≤ t*‖u‖^2 by positivity)]
  have hterm₁ : (1/t)*‖Q u-u‖ ≤ κ*‖u‖/t := by
    have h := mul_le_mul_of_nonneg_left (hQ u) (by positivity : 0 ≤ 1/t)
    convert h using 1 <;> ring
  have hterm₂ : |1/t-1/‖u‖^2| * ‖u‖ ≤ κ*‖u‖/t := by
    rw [hrecip]
    calc
      |t-‖u‖^2|/(t*‖u‖^2)*‖u‖ = |t-‖u‖^2| * (‖u‖/(t*‖u‖^2)) := by ring
      _ ≤ (κ*‖u‖^2)*(‖u‖/(t*‖u‖^2)) :=
        mul_le_mul_of_nonneg_right hform (by positivity)
      _ = κ*‖u‖/t := by field_simp [htne,hsne]
  have hid : (1/t) • Q u-(1/‖u‖^2) • u =
      (1/t) • (Q u-u)+(1/t-1/‖u‖^2) • u := by module
  change ‖(1/t) • Q u-(1/‖u‖^2) • u‖ ≤ _
  rw [hid]
  have htriangle := norm_add_le ((1/t) • (Q u-u)) ((1/t-1/‖u‖^2) • u)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1/t)] at htriangle
  have hbound : 2*κ*‖u‖/t ≤ 4*κ := by
    apply (div_le_iff₀ htpos).2
    have h := mul_le_mul_of_nonneg_left htge (by positivity : 0 ≤ 4*κ)
    linarith only [h]
  calc
    ‖(1/t) • (Q u-u)+(1/t-1/‖u‖^2) • u‖ ≤
        (1/t)*‖Q u-u‖+|1/t-1/‖u‖^2| * ‖u‖ := htriangle
    _ ≤ κ*‖u‖/t+κ*‖u‖/t := add_le_add hterm₁ hterm₂
    _ = 2*κ*‖u‖/t := by ring
    _ ≤ 4*κ := hbound

lemma norm_characteristic_map_sub_inv_le (Q : E →L[ℝ] E) (u ζ : E) (κ : ℝ)
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1/4) (hs : 3/4 ≤ ‖u‖)
    (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖)
    (hζ : inner ℝ ζ (Q ζ) = 1 / inner ℝ u (Q u)) :
    |‖Q ζ‖-1/‖u‖| ≤ 4*κ := by
  let t : ℝ := inner ℝ u (Q u)
  let a : ℝ := inner ℝ ζ (Q ζ)
  let d : ℝ := ‖u‖*‖ζ‖
  have ht := quadratic_form_bounds Q κ hQ u
  have ha := quadratic_form_bounds Q κ hQ ζ
  have hspos : 0 < ‖u‖ := by linarith
  have hsne : ‖u‖ ≠ 0 := ne_of_gt hspos
  have hkm : 0 < 1-κ := by linarith
  have hkp : 0 ≤ 1+κ := by linarith
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  have htne : t ≠ 0 := ne_of_gt htpos
  have hapos : 0 < a := by change 0 < inner ℝ ζ (Q ζ); rw [hζ]; positivity
  have hta : t*a=1 := by
    change t * inner ℝ ζ (Q ζ) = 1
    rw [hζ]
    exact mul_one_div_cancel htne
  have hlow := mul_le_mul ht.1 ha.1 (by positivity) (le_of_lt htpos)
  have hupp := mul_le_mul ht.2 ha.2 (le_of_lt hapos) (by positivity)
  change (1-κ)*‖u‖^2*((1-κ)*‖ζ‖^2) ≤ t*a at hlow
  change t*a ≤ (1+κ)*‖u‖^2*((1+κ)*‖ζ‖^2) at hupp
  rw [hta] at hlow hupp
  have hLsq : ((1-κ)*d)^2 ≤ 1 := by
    calc
      ((1-κ)*d)^2 = (1-κ)*‖u‖^2*((1-κ)*‖ζ‖^2) := by dsimp [d]; ring
      _ ≤ 1 := hlow
  have hUsq : 1 ≤ ((1+κ)*d)^2 := by
    calc
      1 ≤ (1+κ)*‖u‖^2*((1+κ)*‖ζ‖^2) := hupp
      _ = ((1+κ)*d)^2 := by dsimp [d]; ring
  have hd₀ : 0 ≤ d := by dsimp [d]; positivity
  have hL₀ : 0 ≤ (1-κ)*d := mul_nonneg (le_of_lt hkm) hd₀
  have hU₀ : 0 ≤ (1+κ)*d := mul_nonneg hkp hd₀
  have hL : (1-κ)*d ≤ 1 := (sq_le_sq₀ hL₀ (by norm_num)).mp (by simpa using hLsq)
  have hU : 1 ≤ (1+κ)*d := (sq_le_sq₀ (by norm_num) hU₀).mp (by simpa using hUsq)
  have hd₁ : d ≤ 4/3 := by
    have hκd := mul_le_mul_of_nonneg_right hκ₁ hd₀
    linarith only [hL,hκd]
  have hdclose : |d-1| ≤ κ*d := by
    apply abs_le.mpr
    constructor <;> linarith only [hL,hU]
  have hnorm := (abs_norm_sub_norm_le (Q ζ) ζ).trans (hQ ζ)
  have hscaled : |‖u‖*‖Q ζ‖-1| ≤ (8/3)*κ := by
    calc
      |‖u‖*‖Q ζ‖-1| = |‖u‖*(‖Q ζ‖-‖ζ‖)+(d-1)| := by dsimp [d]; congr 1; ring
      _ ≤ |‖u‖*(‖Q ζ‖-‖ζ‖)|+|d-1| := abs_add_le _ _
      _ = ‖u‖*|‖Q ζ‖-‖ζ‖|+|d-1| := by rw [abs_mul,abs_of_nonneg (norm_nonneg u)]
      _ ≤ ‖u‖*(κ*‖ζ‖)+κ*d := add_le_add
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg u)) hdclose
      _ = 2*κ*d := by dsimp [d]; ring
      _ ≤ (8/3)*κ := by
        have h := mul_le_mul_of_nonneg_left hd₁ (by positivity : 0 ≤ 2*κ)
        linarith only [h]
  have hid : ‖u‖*(‖Q ζ‖-1/‖u‖) = ‖u‖*‖Q ζ‖-1 := by field_simp [hsne]
  rw [← hid,abs_mul,abs_of_nonneg (norm_nonneg u)] at hscaled
  have hmuls := mul_le_mul_of_nonneg_right hs (abs_nonneg (‖Q ζ‖-1/‖u‖))
  linarith only [hscaled,hmuls,hκ₀]

theorem injective_of_norm_sub_id_le (Q : E →L[ℝ] E) (κ : ℝ)
    (hκ : κ < 1) (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) : Function.Injective Q := by
  intro x y hxy
  have hzero : Q (x-y)=0 := by rw [map_sub,hxy,sub_self]
  have h := hQ (x-y)
  rw [hzero,zero_sub,norm_neg] at h
  have hz : ‖x-y‖=0 := by
    by_contra hn
    have hp : 0 < ‖x-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hmul := mul_lt_mul_of_pos_right hκ hp
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem bijective_of_norm_sub_id_le [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] E) (κ : ℝ)
    (hκ : κ < 1) (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) : Function.Bijective Q := by
  have hi := injective_of_norm_sub_id_le Q κ hκ hQ
  exact ⟨hi,LinearMap.surjective_of_injective (f := Q.toLinearMap) hi⟩

theorem quadratic_form_pos_of_norm_sub_id_le (Q : E →L[ℝ] E) (κ : ℝ)
    (hκ : κ < 1) (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) (z : E) (hz : z ≠ 0) :
    0 < inner ℝ z (Q z) := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hκ' : 0 < 1-κ := by linarith
  exact lt_of_lt_of_le (by positivity) (quadratic_form_bounds Q κ hQ z).1

theorem normalized_characteristic_constraints (Q : E →L[ℝ] E) (u ζ : E)
    (hQsym : Q.toLinearMap.IsSymmetric) (ht : inner ℝ u (Q u) ≠ 0)
    (huζ : inner ℝ u (Q ζ)=0)
    (hζ : inner ℝ ζ (Q ζ)=1 / inner ℝ u (Q u)) :
    inner ℝ u ((1 / inner ℝ u (Q u)) • Q u)=1 ∧
    inner ℝ ((1 / inner ℝ u (Q u)) • u)
      (Q ((1 / inner ℝ u (Q u)) • u))=inner ℝ ζ (Q ζ) ∧
    inner ℝ ((1 / inner ℝ u (Q u)) • u) (Q ζ)=0 ∧
    inner ℝ ζ (Q ((1 / inner ℝ u (Q u)) • u))=0 := by
  have hcross : inner ℝ ((1 / inner ℝ u (Q u)) • u) (Q ζ)=0 := by
    simp [inner_smul_left,huζ]
  refine ⟨?_,?_,hcross,?_⟩
  · rw [real_inner_smul_right]
    field_simp [ht]
  · rw [hζ,map_smul,real_inner_smul_left,real_inner_smul_right]
    field_simp [ht]
  · change inner ℝ ζ (Q.toLinearMap ((1 / inner ℝ u (Q u)) • u)) = 0
    rw [← hQsym ζ ((1 / inner ℝ u (Q u)) • u),real_inner_comm]
    exact hcross

theorem characteristic_vectors_close_to_euclidean (Q : E →L[ℝ] E)
    (ω b ζ : E) (κ : ℝ) (hω : ‖ω‖=1) (hb : ‖b‖≤1/4)
    (hκ₀ : 0≤κ) (hκ₁ : κ≤1/16)
    (hQ : ‖Q-ContinuousLinearMap.id ℝ E‖≤κ)
    (huζ : inner ℝ (ω+b) (Q ζ)=0)
    (hζ : inner ℝ ζ (Q ζ)=1 / inner ℝ (ω+b) (Q (ω+b))) :
    ‖(1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)-
      (1 / ‖ω+b‖^2) • (ω+b)‖≤4*κ ∧
    ∃ w₀ : E, inner ℝ (ω+b) w₀=0 ∧ ‖w₀‖=1 / ‖ω+b‖ ∧ ‖Q ζ-w₀‖≤4*κ := by
  have hQ' := norm_map_sub_le_of_opNorm Q κ hQ
  have hs : 3/4≤‖ω+b‖ := by
    have h := norm_add_le (ω+b) (-b)
    simp only [add_neg_cancel_right,norm_neg,hω] at h
    linarith
  have hκquarter : κ≤1/4 := by linarith
  have hreal := norm_normalized_map_sub_le Q (ω+b) κ hκ₀ hκquarter hs hQ'
  have himag := norm_characteristic_map_sub_inv_le Q (ω+b) ζ κ hκ₀ hκquarter hs hQ' hζ
  exact ⟨hreal,exists_shrinking_sphere_model_tangent ω b (Q ζ) (4*κ)
    hω hb (by linarith) huζ himag⟩

theorem characteristic_residual_lower_bound (Q : E →L[ℝ] E)
    (ω b v ζ : E) (κ : ℝ) (hω : ‖ω‖=1) (hb : ‖b‖≤1/4)
    (hv : ‖v‖=1) (hωv : inner ℝ ω v=0)
    (hκ₀ : 0≤κ) (hκ₁ : κ≤1/16)
    (hQ : ‖Q-ContinuousLinearMap.id ℝ E‖≤κ)
    (huζ : inner ℝ (ω+b) (Q ζ)=0)
    (hζ : inner ℝ ζ (Q ζ)=1 / inner ℝ (ω+b) (Q (ω+b))) :
    -64*‖b‖*κ-256*κ^2 ≤
      ‖perpendicularComponent ω
        (ω-(1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))‖^2+
      ‖perpendicularComponent ω (v-Q ζ)‖^2-
      (inner ℝ b ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)))^2-
      (inner ℝ b (Q ζ))^2 := by
  obtain ⟨hq,w₀,hu₀,hw₀,hclose⟩ :=
    characteristic_vectors_close_to_euclidean Q ω b ζ κ hω hb hκ₀ hκ₁ hQ huζ hζ
  have hR := shrinking_sphere_residual_perturbation ω b v w₀
    ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)) (Q ζ) (4*κ)
    hω hv hωv hb (by positivity) hu₀ hw₀ hq hclose
  convert hR using 1 <;> ring

theorem characteristic_hessian_lower_bound (Q : E →L[ℝ] E)
    (ω b v ζ : E) (κ r c β : ℝ) (H : E → E → ℝ)
    (hω : ‖ω‖=1) (hb : ‖b‖≤1/4) (hv : ‖v‖=1) (hωv : inner ℝ ω v=0)
    (hκ₀ : 0≤κ) (hκ₁ : κ≤1/16)
    (hQ : ‖Q-ContinuousLinearMap.id ℝ E‖≤κ)
    (huζ : inner ℝ (ω+b) (Q ζ)=0)
    (hζ : inner ℝ ζ (Q ζ)=1 / inner ℝ (ω+b) (Q (ω+b)))
    (hc : 0≤c) (hβ : 0≤β) (hH : ∀ x, H x x≤-(c*β)*‖x‖^2) :
    (1/2)*c*r^2*β-64*‖b‖*κ-256*κ^2 ≤
      ‖perpendicularComponent ω
        (ω-(1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))‖^2+
      ‖perpendicularComponent ω (v-Q ζ)‖^2-
      (inner ℝ b ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)))^2-
      (inner ℝ b (Q ζ))^2-
      r^2*(H ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))
        ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))+H (Q ζ) (Q ζ)) := by
  obtain ⟨hq,w₀,hu₀,hw₀,hclose⟩ :=
    characteristic_vectors_close_to_euclidean Q ω b ζ κ hω hb hκ₀ hκ₁ hQ huζ hζ
  have hR := shrinking_sphere_perturbed_hessian_lower_bound ω b v w₀
    ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)) (Q ζ) (4*κ) r c β H
    hω hv hωv hb (by positivity) (by linarith) hu₀ hw₀ hq hclose hc hβ hH
  convert hR using 1 <;> ring

#print axioms characteristic_vectors_close_to_euclidean
#print axioms characteristic_residual_lower_bound
#print axioms characteristic_hessian_lower_bound
#print axioms normalized_characteristic_constraints
#print axioms bijective_of_norm_sub_id_le


theorem exists_linear_inverse_of_norm_sub_id_le [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] E) (κ : ℝ) (hκ : κ < 1)
    (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖) :
    ∃ M : E →ₗ[ℝ] E, (∀ z, Q (M z)=z) ∧ (∀ z, M (Q z)=z) := by
  let e := LinearEquiv.ofBijective Q.toLinearMap
    (bijective_of_norm_sub_id_le Q κ hκ hQ)
  refine ⟨e.symm.toLinearMap,?_,?_⟩
  · intro z
    change e (e.symm z)=z
    exact e.apply_symm_apply z
  · intro z
    change e.symm (e z)=z
    exact e.symm_apply_apply z

theorem inverse_metric_characteristic_constraints (Q : E →L[ℝ] E)
    (M : E →ₗ[ℝ] E) (u w : E) (hQsym : Q.toLinearMap.IsSymmetric)
    (hQM : ∀ z, Q (M z)=z) (hMQ : ∀ z, M (Q z)=z)
    (ht : inner ℝ u (Q u) ≠ 0) (huw : inner ℝ u w=0)
    (hw : inner ℝ w (M w)=1 / inner ℝ u (Q u)) :
    inner ℝ u ((1 / inner ℝ u (Q u)) • Q u)=1 ∧
    inner ℝ ((1 / inner ℝ u (Q u)) • Q u)
      (M ((1 / inner ℝ u (Q u)) • Q u))=inner ℝ w (M w) ∧
    inner ℝ ((1 / inner ℝ u (Q u)) • Q u) (M w)=0 ∧
    inner ℝ w (M ((1 / inner ℝ u (Q u)) • Q u))=0 := by
  have hMq : M ((1 / inner ℝ u (Q u)) • Q u) =
      (1 / inner ℝ u (Q u)) • u := by rw [map_smul,hMQ]
  have hcross : inner ℝ (Q u) (M w)=0 := by
    change inner ℝ (Q.toLinearMap u) (M w)=0
    rw [hQsym]
    change inner ℝ u (Q (M w))=0
    rw [hQM,huw]
  refine ⟨?_,?_,?_,?_⟩
  · rw [real_inner_smul_right]
    field_simp [ht]
  · rw [hw,hMq,real_inner_smul_right,real_inner_smul_left,real_inner_comm]
    field_simp [ht]
  · rw [real_inner_smul_left,hcross,mul_zero]
  · have hwu : inner ℝ w u=0 := (real_inner_comm u w).trans huw
    rw [hMq,real_inner_smul_right,hwu,mul_zero]

theorem inverse_metric_vectors_close_to_euclidean (Q : E →L[ℝ] E)
    (M : E →ₗ[ℝ] E) (ω b w : E) (κ : ℝ)
    (hω : ‖ω‖=1) (hb : ‖b‖ ≤ 1/4) (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1/16)
    (hQ : ‖Q-ContinuousLinearMap.id ℝ E‖ ≤ κ) (hQM : ∀ z, Q (M z)=z)
    (huw : inner ℝ (ω+b) w=0)
    (hw : inner ℝ w (M w)=1 / inner ℝ (ω+b) (Q (ω+b))) :
    ‖(1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)-
      (1 / ‖ω+b‖^2) • (ω+b)‖ ≤ 4*κ ∧
    ∃ w₀ : E, inner ℝ (ω+b) w₀=0 ∧ ‖w₀‖=1 / ‖ω+b‖ ∧ ‖w-w₀‖ ≤ 4*κ := by
  have hζ : inner ℝ (M w) (Q (M w))=1 / inner ℝ (ω+b) (Q (ω+b)) := by
    rw [hQM,real_inner_comm,hw]
  have h := characteristic_vectors_close_to_euclidean Q ω b (M w) κ
    hω hb hκ₀ hκ₁ hQ (by rw [hQM,huw]) hζ
  simpa only [hQM] using h

theorem inverse_metric_residual_lower_bound (Q : E →L[ℝ] E)
    (M : E →ₗ[ℝ] E) (ω b v w : E) (κ : ℝ)
    (hω : ‖ω‖=1) (hb : ‖b‖ ≤ 1/4) (hv : ‖v‖=1) (hωv : inner ℝ ω v=0)
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1/16)
    (hQ : ‖Q-ContinuousLinearMap.id ℝ E‖ ≤ κ) (hQM : ∀ z, Q (M z)=z)
    (huw : inner ℝ (ω+b) w=0)
    (hw : inner ℝ w (M w)=1 / inner ℝ (ω+b) (Q (ω+b))) :
    -64*‖b‖*κ-256*κ^2 ≤
      ‖perpendicularComponent ω
        (ω-(1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))‖^2+
      ‖perpendicularComponent ω (v-w)‖^2-
      (inner ℝ b ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)))^2-
      (inner ℝ b w)^2 := by
  have hζ : inner ℝ (M w) (Q (M w))=1 / inner ℝ (ω+b) (Q (ω+b)) := by
    rw [hQM,real_inner_comm,hw]
  have h := characteristic_residual_lower_bound Q ω b v (M w) κ
    hω hb hv hωv hκ₀ hκ₁ hQ (by rw [hQM,huw]) hζ
  simpa only [hQM] using h

theorem inverse_metric_hessian_lower_bound (Q : E →L[ℝ] E)
    (M : E →ₗ[ℝ] E) (ω b v w : E) (κ r c β : ℝ) (H : E → E → ℝ)
    (hω : ‖ω‖=1) (hb : ‖b‖ ≤ 1/4) (hv : ‖v‖=1) (hωv : inner ℝ ω v=0)
    (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1/16)
    (hQ : ‖Q-ContinuousLinearMap.id ℝ E‖ ≤ κ) (hQM : ∀ z, Q (M z)=z)
    (huw : inner ℝ (ω+b) w=0)
    (hw : inner ℝ w (M w)=1 / inner ℝ (ω+b) (Q (ω+b)))
    (hc : 0 ≤ c) (hβ : 0 ≤ β) (hH : ∀ x, H x x ≤ -(c*β)*‖x‖^2) :
    (1/2)*c*r^2*β-64*‖b‖*κ-256*κ^2 ≤
      ‖perpendicularComponent ω
        (ω-(1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))‖^2+
      ‖perpendicularComponent ω (v-w)‖^2-
      (inner ℝ b ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b)))^2-
      (inner ℝ b w)^2-
      r^2*(H ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))
        ((1 / inner ℝ (ω+b) (Q (ω+b))) • Q (ω+b))+H w w) := by
  have hζ : inner ℝ (M w) (Q (M w))=1 / inner ℝ (ω+b) (Q (ω+b)) := by
    rw [hQM,real_inner_comm,hw]
  have h := characteristic_hessian_lower_bound Q ω b v (M w) κ r c β H
    hω hb hv hωv hκ₀ hκ₁ hQ (by rw [hQM,huw]) hζ hc hβ hH
  simpa only [hQM] using h

#print axioms exists_linear_inverse_of_norm_sub_id_le
#print axioms inverse_metric_characteristic_constraints
#print axioms inverse_metric_vectors_close_to_euclidean
#print axioms inverse_metric_residual_lower_bound
#print axioms inverse_metric_hessian_lower_bound


lemma opNorm_sub_id_le_of_sandwich (Q L A : E →L[ℝ] E)
    (hQ : Q-ContinuousLinearMap.id ℝ E=(L.comp A).comp L) :
    ‖Q-ContinuousLinearMap.id ℝ E‖ ≤ ‖L‖^2*‖A‖ := by
  rw [hQ]
  calc
    ‖(L.comp A).comp L‖ ≤ ‖L.comp A‖*‖L‖ :=
      ContinuousLinearMap.opNorm_comp_le (L.comp A) L
    _ ≤ (‖L‖*‖A‖)*‖L‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le L A) (norm_nonneg L)
    _ = ‖L‖^2*‖A‖ := by ring

#print axioms opNorm_sub_id_le_of_sandwich

end OAI.AnisotropicCalderon.ShrinkingMetricBridge
