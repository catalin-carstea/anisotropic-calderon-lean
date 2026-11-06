import Calderon.ActualUniformScalarCutoffCommutator
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
namespace OAI.AnisotropicCalderon.ConstantForcingHalfNorm

private lemma norm_sum_three_le
    {W : Type*} [NormedAddCommGroup W] (v : Fin 3 → W) (C : ℝ)
    (h : ∀ i : Fin 3, ‖v i‖ ≤ C) : ‖∑ i : Fin 3, v i‖ ≤ 3*C := by
  calc
    _ ≤ ∑ i : Fin 3, ‖v i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, C := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

private lemma norm_sum_nine_le
    {W : Type*} [NormedAddCommGroup W] (v : Fin 3 → Fin 3 → W) (C : ℝ)
    (h : ∀ i j : Fin 3, ‖v i j‖ ≤ C) : ‖∑ i : Fin 3, ∑ j : Fin 3, v i j‖ ≤ 9*C := by
  have hRows (i : Fin 3) := norm_sum_three_le (v i) C (h i)
  exact (norm_sum_three_le (fun i => ∑ j : Fin 3, v i j) (3*C) hRows).trans_eq (by ring)

theorem sum_div_smul_eq_inverse_smul_sum
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (r : ℝ) (sigma : Fin 3 → Fin 3 → ℝ) (D : Fin 3 → Fin 3 → W) :
    (∑ i : Fin 3, ∑ j : Fin 3, (sigma i j/r) • D i j)=
      r⁻¹ • (∑ i : Fin 3, ∑ j : Fin 3, sigma i j • D i j) := by
  simp only [Finset.smul_sum,div_eq_mul_inv,smul_smul]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    congrArg (fun c : ℝ => c • D i j) (mul_comm (sigma i j) r⁻¹)))

theorem norm_complete_constant_forcing_sum_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I : V →L[ℝ] W) (Corr DQ : Fin 3 → V →L[ℝ] W)
    (a k : Fin 3 → V) (Xscaled : Fin 3 → Fin 3 → W)
    (Q : Fin 3 → Fin 3 → ℝ) (Gamma : Fin 3 → Fin 3 → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (s : W) (r M : ℝ) (hM : 1 ≤ M) (hr : |r| ≤ 1) (hs : ‖s‖ ≤ M)
    (hI : ‖I‖ ≤ M) (hCorr : ∀ i, ‖Corr i‖ ≤ M) (hDQ : ∀ i, ‖DQ i‖ ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ M) (hk : ∀ i, ‖k i‖ ≤ M)
    (hX : ∀ i j, ‖Xscaled i j‖ ≤ M)
    (hQ : ∀ i j, |Q i j| ≤ 3) (hGamma : ∀ i j l, |Gamma i j l| ≤ M) (hb : ∀ i, |b i| ≤ M) :
    ‖s+(∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (Corr i (a j)+r • DQ i (a j)+Xscaled i j-r • (∑ l : Fin 3, Gamma i j l • I (k l))))+
      (∑ i : Fin 3, b i • (I (a i)+r • I (k i)))‖ ≤
      M+27*(2*M^2+M+3*M^3)+6*M^3 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hIa (i : Fin 3) : ‖I (a i)‖ ≤ M^2 :=
    (I.le_opNorm _).trans ((mul_le_mul hI (ha i) (norm_nonneg _) hM0).trans_eq (by ring))
  have hIk (i : Fin 3) : ‖I (k i)‖ ≤ M^2 :=
    (I.le_opNorm _).trans ((mul_le_mul hI (hk i) (norm_nonneg _) hM0).trans_eq (by ring))
  have hC (i j : Fin 3) : ‖Corr i (a j)‖ ≤ M^2 :=
    ((Corr i).le_opNorm _).trans ((mul_le_mul (hCorr i) (ha j) (norm_nonneg _) hM0).trans_eq (by ring))
  have hD (i j : Fin 3) : ‖r • DQ i (a j)‖ ≤ M^2 := by
    have hValue : ‖DQ i (a j)‖ ≤ M^2 :=
      ((DQ i).le_opNorm _).trans ((mul_le_mul (hDQ i) (ha j) (norm_nonneg _) hM0).trans_eq (by ring))
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hr hValue (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hConn (i j : Fin 3) : ‖r • (∑ l : Fin 3, Gamma i j l • I (k l))‖ ≤ 3*M^3 := by
    have hTerms (l : Fin 3) : ‖Gamma i j l • I (k l)‖ ≤ M^3 := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul (hGamma i j l) (hIk l) (norm_nonneg _) hM0).trans_eq (by ring)
    have hSum := norm_sum_three_le (fun l : Fin 3 => Gamma i j l • I (k l)) (M^3) hTerms
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hr hSum (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  let A := 2*M^2+M+3*M^3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hReg (i j : Fin 3) :
      ‖Corr i (a j)+r • DQ i (a j)+Xscaled i j-r • (∑ l : Fin 3, Gamma i j l • I (k l))‖ ≤ A := by
    have h1 := norm_add_le (Corr i (a j)) (r • DQ i (a j))
    have h2 := norm_add_le (Corr i (a j)+r • DQ i (a j)) (Xscaled i j)
    have h3 := norm_sub_le (Corr i (a j)+r • DQ i (a j)+Xscaled i j)
      (r • (∑ l : Fin 3, Gamma i j l • I (k l)))
    dsimp [A]
    linarith only [h1,h2,h3,hC i j,hD i j,hX i j,hConn i j]
  have hPrincipal : ‖∑ i : Fin 3, ∑ j : Fin 3, Q i j •
      (Corr i (a j)+r • DQ i (a j)+Xscaled i j-r • (∑ l : Fin 3, Gamma i j l • I (k l)))‖ ≤ 27*A := by
    have hTerms (i j : Fin 3) : ‖Q i j •
        (Corr i (a j)+r • DQ i (a j)+Xscaled i j-r • (∑ l : Fin 3, Gamma i j l • I (k l)))‖ ≤ 3*A := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hQ i j) (hReg i j) (norm_nonneg _) (by norm_num)
    exact (norm_sum_nine_le _ (3*A) hTerms).trans_eq (by ring)
  have hDrift : ‖∑ i : Fin 3, b i • (I (a i)+r • I (k i))‖ ≤ 6*M^3 := by
    have hTerms (i : Fin 3) : ‖b i • (I (a i)+r • I (k i))‖ ≤ 2*M^3 := by
      have hrIk : ‖r • I (k i)‖ ≤ M^2 := by
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul hr (hIk i) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      have hBracket : ‖I (a i)+r • I (k i)‖ ≤ 2*M^2 := by
        linarith only [norm_add_le (I (a i)) (r • I (k i)),hIa i,hrIk]
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul (hb i) hBracket (norm_nonneg _) hM0).trans_eq (by ring)
    exact (norm_sum_three_le _ (2*M^3) hTerms).trans_eq (by ring)
  have h1 := norm_add_le s (∑ i : Fin 3, ∑ j : Fin 3, Q i j •
    (Corr i (a j)+r • DQ i (a j)+Xscaled i j-r • (∑ l : Fin 3, Gamma i j l • I (k l))))
  have h2 := norm_add_le (s+(∑ i : Fin 3, ∑ j : Fin 3, Q i j •
    (Corr i (a j)+r • DQ i (a j)+Xscaled i j-r • (∑ l : Fin 3, Gamma i j l • I (k l)))))
    (∑ i : Fin 3, b i • (I (a i)+r • I (k i)))
  change _ ≤ M+27*A+6*M^3
  linarith only [h1,h2,hs,hPrincipal,hDrift]

end OAI.AnisotropicCalderon.ConstantForcingHalfNorm
