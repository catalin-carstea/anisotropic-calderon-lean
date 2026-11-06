import Calderon.ConnectionError
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_connection_le
    (Q M : E →L[ℝ] E) (DQ DM : E →L[ℝ] E →L[ℝ] E)
    (T : E → E → E) (κ d : ℝ) (hκ : κ≤1/4) (hd : 0≤d)
    (hQ : ∀ z, ‖Q z-z‖≤κ*‖z‖) (hQM : ∀ z, Q (M z)=z)
    (hDQ : ∀ X Z, ‖DQ X Z‖≤d*‖X‖*‖Z‖)
    (hDM : ∀ X Z, DM X Z = -M (DQ X (M Z)))
    (hT : ∀ X Y Z, 2*inner ℝ (M (T X Y)) Z =
      inner ℝ (DM X Y) Z+inner ℝ (DM Y X) Z-inner ℝ (DM Z X) Y)
    (X Y : E) : ‖T X Y‖≤(10/3)*d*‖X‖*‖Y‖ := by
  have hM := norm_inverse_apply_le_four_thirds Q M κ hκ hQ hQM
  have hD := norm_inverse_derivative_apply_le M DQ DM d hd hM hDQ hDM
  have hQ' : ∀ z, ‖Q z‖≤(5/4)*‖z‖ := by
    intro z
    have h := norm_map_le_of_norm_sub_id_le Q κ hQ z
    have hm := mul_le_mul_of_nonneg_right hκ (norm_nonneg z)
    linarith
  have h := norm_connection_le_of_koszul Q M DM T (5/4) ((16/9)*d)
    (by norm_num) (by positivity) hQ' hQM hD hT X Y
  convert h using 1 <;> ring

theorem hessian_connection_error_le
    (T : E → E → E) (ell : E →L[ℝ] ℝ) (q w : E) (r ε d : ℝ)
    (hr : 0≤r) (hε : 0≤ε) (hd : 0≤d) (hdsmall : d≤ε*r)
    (hell : ‖ell‖≤(5/4)*r) (hq : ‖q‖≤2) (hw : ‖w‖≤2)
    (hT : ∀ X Y, ‖T X Y‖≤(10/3)*d*‖X‖*‖Y‖) :
    |ell (T q q)+ell (T w w)|≤(100/3)*ε*r^2 := by
  have hq' : ‖q‖^2≤4 := by nlinarith [norm_nonneg q]
  have hw' : ‖w‖^2≤4 := by nlinarith [norm_nonneg w]
  have hnq : |ell (T q q)|≤‖ell‖*((10/3)*d*‖q‖^2) := by
    have h := (ell.le_opNorm (T q q)).trans
      (mul_le_mul_of_nonneg_left (hT q q) (norm_nonneg ell))
    simpa only [Real.norm_eq_abs,pow_two,mul_assoc] using h
  have hnw : |ell (T w w)|≤‖ell‖*((10/3)*d*‖w‖^2) := by
    have h := (ell.le_opNorm (T w w)).trans
      (mul_le_mul_of_nonneg_left (hT w w) (norm_nonneg ell))
    simpa only [Real.norm_eq_abs,pow_two,mul_assoc] using h
  calc
    |ell (T q q)+ell (T w w)|≤|ell (T q q)|+|ell (T w w)| := abs_add_le _ _
    _ ≤ ‖ell‖*((10/3)*d*‖q‖^2)+‖ell‖*((10/3)*d*‖w‖^2) := add_le_add hnq hnw
    _ = ‖ell‖*((10/3)*d)*(‖q‖^2+‖w‖^2) := by ring
    _ ≤ ((5/4)*r)*((10/3)*d)*8 := mul_le_mul
      (mul_le_mul_of_nonneg_right hell (by positivity)) (by linarith)
      (by positivity) (by positivity)
    _ = (100/3)*r*d := by ring
    _ ≤ (100/3)*r*(ε*r) := mul_le_mul_of_nonneg_left hdsmall (by positivity)
    _ = (100/3)*ε*r^2 := by ring

#print axioms norm_connection_le
#print axioms hessian_connection_error_le
end OAI.AnisotropicCalderon.ConnectionError
