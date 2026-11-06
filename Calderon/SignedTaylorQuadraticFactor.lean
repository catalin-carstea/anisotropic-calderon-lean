import Calderon.SignedOperatorTaylorRemainder

/-! Actual integral, including zero. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma secondTaylorRemainder_sq_smul_zero (F : ℝ → V) (hF : ContDiffAt ℝ ∞ F 0) :
    secondTaylorRemainder (fun t : ℝ => t^2 • F t) 0 = F 0 := by
  let G := fun t : ℝ => t^2 • F t
  let D := fun t : ℝ => (2*t) • F t + t^2 • deriv F t
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ F t := by
    filter_upwards [(hF.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)] with t ht
    exact ht.differentiableAt (by norm_num)
  have hFirst : deriv G =ᶠ[𝓝 (0 : ℝ)] D := by
    filter_upwards [hNear] with t ht
    have h := ((hasDerivAt_id t).pow 2).smul ht.hasDerivAt
    change HasDerivAt G _ t at h
    simpa only [G,D,id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul,add_comm] using h.deriv
  have hDF : ContDiffAt ℝ ∞ (deriv F) 0 := hF.derivWithin (by simp)
  have hD : HasDerivAt D ((2 : ℝ) • F 0) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul 2).smul
      (hF.differentiableAt (by simp)).hasDerivAt).add
      ((((hasDerivAt_id (0 : ℝ)).pow 2).smul
        (hDF.differentiableAt (by simp)).hasDerivAt))
    change HasDerivAt D _ 0 at h
    simpa only [D,id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul,mul_zero,zero_smul,
      add_zero,zero_add,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hSecond : deriv (deriv G) 0 = (2 : ℝ) • F 0 := hFirst.deriv_eq.trans hD.deriv
  rw [secondTaylorRemainder_zero,hSecond,smul_smul]
  norm_num

lemma secondTaylorRemainder_sq_smul (F : ℝ → V) (r : ℝ)
    (hF : ∀ t ∈ uIcc (0 : ℝ) r, ContDiffAt ℝ ∞ F t) :
    secondTaylorRemainder (fun t : ℝ => t^2 • F t) r = F r := by
  have h0 := hF 0 (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) r)
  by_cases hr : r = 0
  · subst r
    exact secondTaylorRemainder_sq_smul_zero F h0
  let G := fun t : ℝ => t^2 • F t
  have hG (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) r) : ContDiffAt ℝ ∞ G t :=
    (contDiffAt_id.pow 2).smul (hF t ht)
  have hG0 : G 0 = 0 := by simp only [G,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_smul]
  have hD0 : deriv G 0 = 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).pow 2).smul (h0.differentiableAt (by simp)).hasDerivAt
    change HasDerivAt G _ 0 at h
    simpa only [G,id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul,mul_zero,zero_smul,
      add_zero,zero_add,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h.deriv
  have hTaylor := signed_taylor_integral_remainder G r hG
  rw [hG0,hD0,smul_zero,zero_add,zero_add] at hTaylor
  have hEq : r^2 • F r = r^2 • secondTaylorRemainder G r := hTaylor
  exact ((smul_right_injective V (pow_ne_zero 2 hr)) hEq).symm

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_sq_smul_zero
#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_sq_smul
