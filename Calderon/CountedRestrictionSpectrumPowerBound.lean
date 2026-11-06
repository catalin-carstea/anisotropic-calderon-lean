import C3Spectral
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable

theorem tsum_rpow_le_of_counted_approx {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (hw : Orthonormal ℝ w) (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i) (M : ℝ) (hM : 0 < M) (hμM : ∀ i, μ i ≤ M)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (s : ℕ) (B : ℝ) (N A0 : ℕ)
    (happrox : ∀ A : ℕ, A0 ≤ A → ∃ P : E →L[ℝ] F,
      FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * A ^ 3 ∧
      ‖R - P‖ * (A : ℝ) ^ s ≤ B)
    (β : ℝ) (hβ : 0 < β) (hsβ : 3 < s * β)
    (K : ℕ) (hK0 : A0 ≤ K) (hBK : B < M*((2:ℝ)^K)^s) :
    (∑' i, μ i ^ β) ≤ (N:ℝ)*8^(K+1)*M^β /
      (1-8*(((2:ℝ)^s)⁻¹)^β) := by
  classical
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hsβ
    linarith
  set a : ℝ := ((2 : ℝ) ^ s)⁻¹ with ha
  have h2s : 1 < (2 : ℝ) ^ s := one_lt_pow₀ (by norm_num) hs
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ h2s
                              
  have hA0 : ∀ m : ℕ, A0 ≤ 2 ^ (m + 1 + K) := fun m =>
    hK0.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hkey : ∀ m : ℕ, a ^ (m + 1) * ((2 : ℝ) ^ (m + 1 + K)) ^ s = ((2 : ℝ) ^ K) ^ s := by
    intro m
    rw [ha, inv_pow, inv_mul_eq_iff_eq_mul₀ (by positivity), ← pow_mul, ← pow_mul, ← pow_mul,
      ← pow_add]
    congr 1
    ring
              
  let J : ℕ → Set ι := fun m => {i | a ^ (m + 1) * M < μ i ∧ μ i ≤ a ^ m * M}
  have huniq : ∀ i m m', i ∈ J m → i ∈ J m' → m ≤ m' := by
    intro i m m' h h'
    by_contra hlt
    push Not at hlt
    have h1 : a ^ m ≤ a ^ (m' + 1) := pow_le_pow_of_le_one ha0.le ha1.le (by omega)
    have h2 := mul_le_mul_of_nonneg_right h1 hM.le
    have h3 : μ i ≤ a ^ m * M := h.2
    have h4 : a ^ (m' + 1) * M < μ i := h'.1
    linarith
  have hcov : ∀ i, ∃! m, i ∈ J m := by
    intro i
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near_of_lt_one (div_pos (hμ i) hM)
      ((div_le_one hM).mpr (hμM i)) ha0 ha1
    have hm : i ∈ J m := ⟨(lt_div_iff₀ hM).mp hm1, (div_le_iff₀ hM).mp hm2⟩
    exact ⟨m, hm, fun m' hm' => le_antisymm (huniq _ _ _ hm' hm) (huniq _ _ _ hm hm')⟩
                      
  let g : ℕ → ℝ := fun m => (N : ℝ) * ((2 : ℝ) ^ (m + 1 + K)) ^ 3 * (a ^ m * M) ^ β
  have hband : ∀ m (t : Finset (J m)), ∑ x ∈ t, μ x ^ β ≤ g m := by
    intro m t
    obtain ⟨P, hPfin, hPrank, hPerr⟩ := happrox (2 ^ (m + 1 + K)) (hA0 m)
    have := hPfin
    have hpow : (0 : ℝ) < ((2 : ℝ) ^ (m + 1 + K)) ^ s := by positivity
    have hlt : ‖R - P‖ < a ^ (m + 1) * M := by
      have he : ‖R - P‖ * ((2 : ℝ) ^ (m + 1 + K)) ^ s ≤ B := by exact_mod_cast hPerr
      have h1 : a ^ (m + 1) * M * ((2 : ℝ) ^ (m + 1 + K)) ^ s = M * ((2 : ℝ) ^ K) ^ s := by
        rw [mul_comm (a ^ (m + 1)) M, mul_assoc, hkey]
      by_contra hge
      push Not at hge
      have := mul_le_mul_of_nonneg_right hge hpow.le
      linarith
    have hcard := card_le_finrank_of_gram R P w hw μ hgram (a ^ (m + 1) * M) (by positivity) hlt
      (t.map (Function.Embedding.subtype _)) (by
        intro i hi
        obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hi
        rw [Function.Embedding.coe_subtype, abs_of_pos (hμ x)]
        exact x.2.1.le)
    rw [Finset.card_map] at hcard
    have hcardR : (t.card : ℝ) ≤ (N : ℝ) * ((2 : ℝ) ^ (m + 1 + K)) ^ 3 := by
      have := hcard.trans hPrank
      exact_mod_cast this
    calc ∑ x ∈ t, μ x ^ β ≤ t.card • (a ^ m * M) ^ β :=
          Finset.sum_le_card_nsmul t _ _ fun x _ => Real.rpow_le_rpow (hμ x).le x.2.2 hβ.le
      _ = (t.card : ℝ) * (a ^ m * M) ^ β := nsmul_eq_mul _ _
      _ ≤ g m := mul_le_mul_of_nonneg_right hcardR (Real.rpow_nonneg (by positivity) _)
                       
  have haβ : a ^ β = ((2 : ℝ) ^ ((s : ℝ) * β))⁻¹ := by
    rw [ha, Real.inv_rpow (by positivity), ← Real.rpow_natCast_mul (by norm_num)]
  have h8 : (8 : ℝ) < (2 : ℝ) ^ ((s : ℝ) * β) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (show ((3 : ℕ) : ℝ) < (s : ℝ) * β by exact_mod_cast hsβ)
    rw [Real.rpow_natCast] at h
    norm_num at h
    exact h
  set q : ℝ := 8 * a ^ β with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq, haβ, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact h8
  have hgeq : g = fun m => ((N : ℝ) * 8 ^ (K + 1) * M ^ β) * q ^ m := by
    funext m
    simp only [g, hq]
    rw [Real.mul_rpow (by positivity) hM.le, ← Real.rpow_pow_comm ha0.le]
    have h83 : ((2 : ℝ) ^ (m + 1 + K)) ^ 3 = 8 ^ (K + 1) * 8 ^ m := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [h83]
    ring
  have hgs : Summable g := by
    rw [hgeq]
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hf : (0 : ι → ℝ) ≤ fun i => μ i ^ β := fun i => Real.rpow_nonneg (hμ i).le β
  have hSum : Summable (fun i => μ i ^ β) :=
    summable_rpow_of_counted_approx R w hw μ hμ M hM hμM hgram s B N A0 happrox β hβ hsβ
  have hPartition := (summable_partition hf hcov).mp hSum
  have hSigma : Summable (fun v : Σ m : ℕ, J m => μ v.2 ^ β) := by
    simpa only [Set.sigmaEquiv,Equiv.coe_fn_mk,Function.comp_def] using hSum.comp_injective (Set.sigmaEquiv J hcov).injective
  have hEquality : (∑' i, μ i ^ β) = ∑' m : ℕ, ∑' i : J m, μ i ^ β := by
    calc
      _ = ∑' v : Σ m : ℕ, J m, μ v.2 ^ β := (Set.sigmaEquiv J hcov).tsum_eq (fun i => μ i ^ β) |>.symm
      _ = _ := hSigma.tsum_sigma' hPartition.1
  have hBound : (∑' i, μ i ^ β) ≤ ∑' m : ℕ, g m := by
    rw [hEquality]
    exact hPartition.2.tsum_le_tsum
      (fun m => Real.tsum_le_of_sum_le (fun x => Real.rpow_nonneg (hμ x).le β) (hband m)) hgs
  have hGeometric : (∑' m : ℕ, g m) = ((N:ℝ)*8^(K+1)*M^β)/(1-q) := by
    rw [hgeq,tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1]
    rfl
  exact hBound.trans_eq hGeometric

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
