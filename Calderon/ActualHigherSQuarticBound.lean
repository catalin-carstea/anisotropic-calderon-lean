import Calderon.ActualHigherSScalarCommutatorForm

/-! Structural quartic bound only. Exact before-code derivation is in
quartic-bound-upfront-v001. Actual same-packet caps and complete word coverage
are mandatory later; no final analytic callback or acceptance is asserted. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticBound
variable {E H N ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

lemma abs_three_operator_pair_le
    (P : H →L[ℝ] N →L[ℝ] ℝ) (A C : E →L[ℝ] H) (B : H →L[ℝ] N) (u : E) :
    |P (A u) (B (C u))| ≤ ‖P‖*‖A‖*‖B‖*‖C‖*‖u‖^2 := by
  have h := ContinuousLinearMap.le_opNorm₂ P (A u) (B (C u))
  calc
    _ ≤ ‖P‖*‖A u‖*‖B (C u)‖ := by simpa only [Real.norm_eq_abs] using h
    _ ≤ ‖P‖*(‖A‖*‖u‖)*(‖B‖*(‖C‖*‖u‖)) := by
      gcongr
      · exact A.le_opNorm u
      · exact (B.le_opNorm (C u)).trans (mul_le_mul_of_nonneg_left (C.le_opNorm u) (norm_nonneg B))
    _ = _ := by ring

lemma abs_three_operator_pair_le_common
    (P : H →L[ℝ] N →L[ℝ] ℝ) (A C : E →L[ℝ] H) (B : H →L[ℝ] N)
    (M : ℝ) (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (hC : ‖C‖ ≤ M) (u : E) :
    |P (A u) (B (C u))| ≤ ‖P‖*M^3*‖u‖^2 := by
  calc
    _ ≤ ‖P‖*‖A‖*‖B‖*‖C‖*‖u‖^2 := abs_three_operator_pair_le P A C B u
    _ ≤ ‖P‖*M*M*M*‖u‖^2 := by gcongr
    _ = _ := by ring

lemma abs_four_pairings_le
    (P : H →L[ℝ] N →L[ℝ] ℝ)
    (A B : ι → E →L[ℝ] H) (G : ι → ι → E →L[ℝ] H)
    (AL : ι → H →L[ℝ] N) (Cl : ι → ι → H →L[ℝ] N)
    (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hB : ∀ i, ‖B i‖ ≤ M)
    (hG : ∀ i j, ‖G i j‖ ≤ M) (hAL : ∀ i, ‖AL i‖ ≤ M)
    (hCl : ∀ i j, ‖Cl i j‖ ≤ M) (u : E) (i j k l : ι) :
    |P (A j u) (Cl i k (A l u))+
      P (A j u) (AL k (G i l u))+
      P (G k j u) (AL l (B i u))+
      P (B k u) (Cl j l (B i u))| ≤ 4*‖P‖*M^3*‖u‖^2 := by
  have h1 := abs_three_operator_pair_le_common P (A j) (A l) (Cl i k) M hM (hA j) (hCl i k) (hA l) u
  have h2 := abs_three_operator_pair_le_common P (A j) (G i l) (AL k) M hM (hA j) (hAL k) (hG i l) u
  have h3 := abs_three_operator_pair_le_common P (G k j) (B i) (AL l) M hM (hG k j) (hAL l) (hB i) u
  have h4 := abs_three_operator_pair_le_common P (B k) (B i) (Cl j l) M hM (hB k) (hCl j l) (hB i) u
  have ht1 := abs_add_le
    (P (A j u) (Cl i k (A l u))+P (A j u) (AL k (G i l u))+
      P (G k j u) (AL l (B i u))) (P (B k u) (Cl j l (B i u)))
  have ht2 := abs_add_le
    (P (A j u) (Cl i k (A l u))+P (A j u) (AL k (G i l u)))
    (P (G k j u) (AL l (B i u)))
  have ht3 := abs_add_le (P (A j u) (Cl i k (A l u))) (P (A j u) (AL k (G i l u)))
  linarith only [h1,h2,h3,h4,ht1,ht2,ht3]

lemma abs_weighted_word_sum_le [Fintype ι]
    (c : ι → ℝ) (R : ι → ι → ℝ) (C r D : ℝ)
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hc : ∀ i, |c i| ≤ C*r) (hR : ∀ i j, |R i j| ≤ D) :
    |∑ i : ι, ∑ j : ι, c i*c j*R i j| ≤ (Fintype.card ι : ℝ)^2*C^2*r^2*D := by
  have hrow (i j : ι) : |c i*c j*R i j| ≤ (C*r)*(C*r)*D := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hc i) (hc j) (abs_nonneg _) (mul_nonneg hC hr)) (hR i j)
      (abs_nonneg _) (mul_nonneg (mul_nonneg hC hr) (mul_nonneg hC hr))
  calc
    _ ≤ ∑ i : ι, |∑ j : ι, c i*c j*R i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, ∑ j : ι, |c i*c j*R i j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, (C*r)*(C*r)*D :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hrow i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

lemma radius_sq_energy_absorption (r beta eta E0 u : ℝ)
    (hr : 0 ≤ r) (hb : 1 ≤ beta) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hsmall : r*beta^2 ≤ eta) (hE : beta*u^2 ≤ E0) :
    r^2*u^2 ≤ eta*E0 := by
  have hb0 : 0 ≤ beta := le_trans zero_le_one hb
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hre : r ≤ eta := (show r ≤ r*beta^2 by nlinarith).trans hsmall
  have hr1 : r ≤ 1 := hre.trans he1
  have hrs : r^2 ≤ eta := (show r^2 ≤ r by nlinarith).trans hre
  have hreb : r^2 ≤ eta*beta := hrs.trans (by nlinarith)
  calc
    _ ≤ (eta*beta)*u^2 := mul_le_mul_of_nonneg_right hreb (sq_nonneg u)
    _ = eta*(beta*u^2) := by ring
    _ ≤ eta*E0 := mul_le_mul_of_nonneg_left hE he
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSQuarticBound
