import Calderon.ActualPhysicalLowResidualIntegralCap
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPhysicalNormAbsorption

lemma original_low_products_budget_of_beta_floor
    (CL CP cRaise : ℝ) (hCL : 0 ≤ CL) (hc : 0 < cRaise) :
    let BF0 : ℝ := 1+8*(4*CL+2*CP^2)/cRaise
    1 ≤ BF0 ∧ 0 < BF0 ∧
    ∀ BF : ℝ,BF0 ≤ BF → ∀ eta : ℝ,0 ≤ eta → eta ≤ 1 →
      2*CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)+2*CP^2*eta^4*(BF^9)⁻¹ ≤ cRaise/8 := by
  dsimp only
  let K : ℝ := 4*CL+2*CP^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hFrac : 0 ≤ 8*K/cRaise := div_nonneg (mul_nonneg (by norm_num) hK) hc.le
  have hFloor1 : 1 ≤ 1+8*(4*CL+2*CP^2)/cRaise := by
    change 1 ≤ 1+8*K/cRaise
    linarith
  refine ⟨hFloor1,zero_lt_one.trans_le hFloor1,?_⟩
  intro BF hFloor eta heta heta1
  have hBF : 1 ≤ BF := hFloor1.trans hFloor
  have hBF0 : 0 < BF := zero_lt_one.trans_le hBF
  have hP2 : 0 < BF^2 := pow_pos hBF0 2
  have hP4 : 0 < BF^4 := pow_pos hBF0 4
  have hP9 : 0 < BF^9 := pow_pos hBF0 9
  have hInv4 : (BF^4)⁻¹ ≤ (BF^2)⁻¹ :=
    (inv_le_inv₀ hP4 hP2).2 (pow_le_pow_right₀ hBF (by decide : (2 : ℕ) ≤ 4))
  have hInv9 : (BF^9)⁻¹ ≤ (BF^2)⁻¹ :=
    (inv_le_inv₀ hP9 hP2).2 (pow_le_pow_right₀ hBF (by decide : (2 : ℕ) ≤ 9))
  have heta2 : eta^2 ≤ 1 := pow_le_one₀ heta heta1
  have heta4 : eta^4 ≤ 1 := pow_le_one₀ heta heta1
  have hTerm4 : eta^2*(BF^4)⁻¹ ≤ (BF^2)⁻¹ := by
    calc
      _ ≤ 1*(BF^4)⁻¹ := mul_le_mul_of_nonneg_right heta2 (inv_nonneg.mpr hP4.le)
      _ = (BF^4)⁻¹ := one_mul _
      _ ≤ _ := hInv4
  have hTerm9 : eta^4*(BF^9)⁻¹ ≤ (BF^2)⁻¹ := by
    calc
      _ ≤ 1*(BF^9)⁻¹ := mul_le_mul_of_nonneg_right heta4 (inv_nonneg.mpr hP9.le)
      _ = (BF^9)⁻¹ := one_mul _
      _ ≤ _ := hInv9
  have hAlpha : 2*CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)+
      2*CP^2*eta^4*(BF^9)⁻¹ ≤ K*(BF^2)⁻¹ := by
    calc
      _ = 2*CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)+2*CP^2*(eta^4*(BF^9)⁻¹) := by ring
      _ ≤ 2*CL*((BF^2)⁻¹+(BF^2)⁻¹)+2*CP^2*(BF^2)⁻¹ :=
        add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hTerm4) (mul_nonneg (by norm_num) hCL))
          (mul_le_mul_of_nonneg_left hTerm9 (mul_nonneg (by norm_num) (sq_nonneg CP)))
      _ = _ := by dsimp only [K]; ring
  have hFracBF : 8*K/cRaise ≤ BF := by
    change 1+8*K/cRaise ≤ BF at hFloor
    linarith
  have hKBF : 8*K ≤ BF*cRaise := (div_le_iff₀ hc).mp hFracBF
  have hBF2 : BF ≤ BF^2 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hBF (by decide : (1 : ℕ) ≤ 2))
  have hKPow : K ≤ (cRaise/8)*BF^2 := by
    have hMul := mul_le_mul_of_nonneg_left hBF2 hc.le
    nlinarith
  calc
    _ ≤ K*(BF^2)⁻¹ := hAlpha
    _ ≤ ((cRaise/8)*BF^2)*(BF^2)⁻¹ :=
      mul_le_mul_of_nonneg_right hKPow (inv_nonneg.mpr hP2.le)
    _ = cRaise/8 := by rw [mul_assoc,mul_inv_cancel₀ hP2.ne',mul_one]

-- Pure complete norm/integral algebra. Production specialization must derive these
-- specific budget premises from their actual qualified owners; it is not completion.
lemma weighted_full_norm_lower_of_low_products_budgets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : R3 → ℝ) (hmu : Continuous mu) (hmu0 : ∀ x,0 ≤ mu x)
    (base low prod full : R3 → E)
    (hb : Continuous base) (hbC : HasCompactSupport base)
    (hl : Continuous low) (hlC : HasCompactSupport low)
    (hp : Continuous prod) (hpC : HasCompactSupport prod)
    (hf : Continuous full) (hfC : HasCompactSupport full)
    (hfull : ∀ x,full x=base x+low x+prod x)
    (IE cRaise CL CP BF eta : ℝ) (hIE : 0 ≤ IE) (hc : 0 < cRaise)
    (hBF : 1 ≤ BF)
    (hBase : (cRaise/2)*IE ≤ ∫ x,mu x*‖base x‖^2)
    (hLow : (∫ x,mu x*‖low x‖^2) ≤ CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)*IE)
    (hProd : BF^9*(∫ x,mu x*‖prod x‖^2) ≤ CP^2*eta^4*IE)
    (hBudget : 2*CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)+
      2*CP^2*eta^4*(BF^9)⁻¹ ≤ cRaise/8) :
    0 < cRaise/8 ∧ (cRaise/8)*IE ≤ ∫ x,mu x*‖full x‖^2 := by
  have hIntegrable (f : R3 → E) (hcont : Continuous f) (hcompact : HasCompactSupport f) :
      Integrable (fun x => mu x*‖f x‖^2) := by
    have hWeightedCompact : HasCompactSupport (fun x => mu x*‖f x‖^2) := by
      apply hcompact.mono
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hz
      apply hx
      simp only [hz,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero]
    exact (hmu.mul (hcont.norm.pow 2)).integrable_of_hasCompactSupport hWeightedCompact
  let R : R3 → E := fun x => low x+prod x
  have hIB := hIntegrable base hb hbC
  have hIL := hIntegrable low hl hlC
  have hIP := hIntegrable prod hp hpC
  have hIF := hIntegrable full hf hfC
  have hIR : Integrable (fun x => mu x*‖R x‖^2) :=
    hIntegrable R (hl.add hp) (hlC.add hpC)
  have hTwo (a b : E) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
    have ht := norm_add_le a b
    nlinarith [norm_nonneg a,norm_nonneg b,norm_nonneg (a+b),sq_nonneg (‖a‖-‖b‖)]
  have hRPoint (x : R3) : mu x*‖R x‖^2 ≤
      2*(mu x*‖low x‖^2)+2*(mu x*‖prod x‖^2) := by
    have hw := mul_le_mul_of_nonneg_left (hTwo (low x) (prod x)) (hmu0 x)
    dsimp only [R]
    nlinarith only [hw]
  have hRIntegral : (∫ x,mu x*‖R x‖^2) ≤
      2*(∫ x,mu x*‖low x‖^2)+2*(∫ x,mu x*‖prod x‖^2) := by
    have hAdd : (∫ x,2*(mu x*‖low x‖^2)+2*(mu x*‖prod x‖^2))=
        (∫ x,2*(mu x*‖low x‖^2))+(∫ x,2*(mu x*‖prod x‖^2)) := by
      simpa only [Pi.add_apply] using integral_add (hIL.const_mul 2) (hIP.const_mul 2)
    calc
      _ ≤ ∫ x,2*(mu x*‖low x‖^2)+2*(mu x*‖prod x‖^2) :=
        integral_mono hIR ((hIL.const_mul 2).add (hIP.const_mul 2)) hRPoint
      _ = _ := by rw [hAdd,integral_const_mul,integral_const_mul]
  have hBF0 : 0 < BF := zero_lt_one.trans_le hBF
  have hBF9 : 0 < BF^9 := pow_pos hBF0 9
  have hProdUnscaled : (∫ x,mu x*‖prod x‖^2) ≤
      (CP^2*eta^4*(BF^9)⁻¹)*IE := by
    have hDiv : (∫ x,mu x*‖prod x‖^2) ≤ (CP^2*eta^4*IE)/(BF^9) :=
      (le_div_iff₀ hBF9).2 (by simpa only [mul_comm] using hProd)
    calc
      _ ≤ (CP^2*eta^4*IE)/(BF^9) := hDiv
      _ = _ := by rw [div_eq_mul_inv]; ring
  let alpha : ℝ := 2*CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)+2*CP^2*eta^4*(BF^9)⁻¹
  have hRBound : (∫ x,mu x*‖R x‖^2) ≤ alpha*IE := by
    calc
      _ ≤ 2*(∫ x,mu x*‖low x‖^2)+2*(∫ x,mu x*‖prod x‖^2) := hRIntegral
      _ ≤ 2*(CL*((BF^2)⁻¹+eta^2*(BF^4)⁻¹)*IE)+
          2*((CP^2*eta^4*(BF^9)⁻¹)*IE) :=
        add_le_add (mul_le_mul_of_nonneg_left hLow (by norm_num))
          (mul_le_mul_of_nonneg_left hProdUnscaled (by norm_num))
      _ = _ := by dsimp only [alpha]; ring
  have hBaseFun (x : R3) : base x=full x+(-R x) := by
    rw [hfull x]
    dsimp only [R]
    abel
  have hBasePoint (x : R3) : mu x*‖base x‖^2 ≤
      2*(mu x*‖full x‖^2)+2*(mu x*‖R x‖^2) := by
    have ht := hTwo (full x) (-R x)
    rw [norm_neg,← hBaseFun x] at ht
    have hw := mul_le_mul_of_nonneg_left ht (hmu0 x)
    nlinarith only [hw]
  have hBaseIntegral : (∫ x,mu x*‖base x‖^2) ≤
      2*(∫ x,mu x*‖full x‖^2)+2*(∫ x,mu x*‖R x‖^2) := by
    have hAdd : (∫ x,2*(mu x*‖full x‖^2)+2*(mu x*‖R x‖^2))=
        (∫ x,2*(mu x*‖full x‖^2))+(∫ x,2*(mu x*‖R x‖^2)) := by
      simpa only [Pi.add_apply] using integral_add (hIF.const_mul 2) (hIR.const_mul 2)
    calc
      _ ≤ ∫ x,2*(mu x*‖full x‖^2)+2*(mu x*‖R x‖^2) :=
        integral_mono hIB ((hIF.const_mul 2).add (hIR.const_mul 2)) hBasePoint
      _ = _ := by rw [hAdd,integral_const_mul,integral_const_mul]
  have hBudgetIE : alpha*IE ≤ (cRaise/8)*IE :=
    mul_le_mul_of_nonneg_right hBudget hIE
  refine ⟨div_pos hc (by norm_num),?_⟩
  nlinarith only [hBase,hBaseIntegral,hRBound,hBudgetIE]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPhysicalNormAbsorption
