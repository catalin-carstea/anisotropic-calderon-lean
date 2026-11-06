import MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.StrictWeightCarleman
theorem uniform_rank_one_coercivity_on_compact_parameter_space
    {X : Type*} [TopologicalSpace X] [T2Space X] {K : Set X} (hK : IsCompact K)
    (Q ℓ : X → (Fin 3 → ℝ) → ℝ)
    (hQc : Continuous (fun p : X × (Fin 3 → ℝ) => Q p.1 p.2))
    (hℓc : Continuous (fun p : X × (Fin 3 → ℝ) => ℓ p.1 p.2))
    (hQh : ∀ x (c : ℝ) ξ, Q x (c • ξ) = c ^ 2 * Q x ξ)
    (hℓh : ∀ x (c : ℝ) ξ, ℓ x (c • ξ) = c * ℓ x ξ)
    (hpos : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → ℓ x ξ = 0 → 0 < Q x ξ) :
    ∃ D α : ℝ, 0 ≤ D ∧ 0 < α ∧ ∀ x ∈ K, ∀ ξ : Fin 3 → ℝ,
      α * ∑ i, ξ i ^ 2 ≤ Q x ξ + D * ℓ x ξ ^ 2 := by
  set S : Set (Fin 3 → ℝ) := Metric.sphere 0 1 with hSdef
  set T : Set (X × (Fin 3 → ℝ)) := K ×ˢ S with hTdef
  have hT : IsCompact T := hK.prod (isCompact_sphere 0 1)
  set F : ℕ → X × (Fin 3 → ℝ) → ℝ := fun n p => Q p.1 p.2 + (n : ℝ) * ℓ p.1 p.2 ^ 2 with hF
  have hFc : ∀ n, Continuous (F n) := fun n => hQc.add (continuous_const.mul (hℓc.pow 2))
  set C : ℕ → Set (X × (Fin 3 → ℝ)) := fun n => T ∩ F n ⁻¹' Set.Iic 0 with hC
  have hCcl : ∀ n, IsClosed (C n) := fun n =>
    hT.isClosed.inter (isClosed_Iic.preimage (hFc n))
  have hCc : ∀ n, IsCompact (C n) := fun n => hT.of_isClosed_subset (hCcl n) Set.inter_subset_left
  have hmono : ∀ n n', n ≤ n' → C n' ⊆ C n := by
    intro n n' hnn p hp
    refine ⟨hp.1, ?_⟩
    have h1 : F n' p ≤ 0 := hp.2
    have h2 : F n p ≤ F n' p := by
      simp only [hF]
      have : (n : ℝ) ≤ n' := by exact_mod_cast hnn
      nlinarith [sq_nonneg (ℓ p.1 p.2)]
    exact le_trans h2 h1
  have hempty : ∃ n, C n = ∅ := by
    by_contra hne
    push_neg at hne
    have hdir : Directed (· ⊇ ·) C := fun n n' =>
      ⟨max n n', hmono n _ (le_max_left _ _), hmono n' _ (le_max_right _ _)⟩
    obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir
      (fun n => hne n) hCc hCcl
    rw [Set.mem_iInter] at hp
    have hpT : p ∈ T := (hp 0).1
    have hle : ∀ n : ℕ, Q p.1 p.2 + (n : ℝ) * ℓ p.1 p.2 ^ 2 ≤ 0 := fun n => (hp n).2
    have hℓ0 : ℓ p.1 p.2 = 0 := by
      by_contra hℓ
      have hsq : 0 < ℓ p.1 p.2 ^ 2 := by positivity
      obtain ⟨n, hn⟩ := exists_nat_gt (-Q p.1 p.2 / ℓ p.1 p.2 ^ 2)
      have h1 := hle n
      rw [div_lt_iff₀ hsq] at hn
      linarith
    have hξ : p.2 ≠ 0 := by
      intro h0
      have h1 : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hpT.2
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hQ := hpos p.1 hpT.1 p.2 hξ hℓ0
    have h0 := hle 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h0
    linarith
  obtain ⟨n, hn⟩ := hempty
  have hFpos : ∀ p ∈ T, 0 < F n p := by
    intro p hp
    by_contra h
    push_neg at h
    have : p ∈ C n := ⟨hp, h⟩
    rw [hn] at this
    exact this
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · exact ⟨n, 1, Nat.cast_nonneg n, one_pos, by simp [hK0]⟩
  have hSne : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hTne : T.Nonempty := hKne.prod hSne
  obtain ⟨p0, hp0, hmin⟩ := hT.exists_isMinOn hTne (hFc n).continuousOn
  have hα0 : 0 < F n p0 := hFpos p0 hp0
  have hα3 : 0 < F n p0 / 3 := div_pos hα0 (by norm_num)
  refine ⟨n, F n p0 / 3, Nat.cast_nonneg n, hα3, ?_⟩
  intro x hx ξ
  have hQ0 : Q x 0 = 0 := by
    have := hQh x 0 0
    rw [smul_zero] at this
    rw [this]; ring
  have hℓ0 : ℓ x 0 = 0 := by
    have := hℓh x 0 0
    rw [smul_zero] at this
    rw [this]; ring
  by_cases hξ : ξ = 0
  · subst hξ
    simp [hQ0, hℓ0]
  have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set η : Fin 3 → ℝ := ‖ξ‖⁻¹ • ξ with hη
  have hηS : (x, η) ∈ T := by
    refine ⟨hx, ?_⟩
    show η ∈ Metric.sphere (0 : Fin 3 → ℝ) 1
    rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hmin' : F n p0 ≤ F n (x, η) := hmin hηS
  have hξη : ξ = ‖ξ‖ • η := by
    rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hFξ : Q x ξ + (n : ℝ) * ℓ x ξ ^ 2 = ‖ξ‖ ^ 2 * F n (x, η) := by
    conv_lhs => rw [hξη, hQh, hℓh]
    simp only [hF]
    ring
  have h3 := sum_sq_le_three_norm_sq ξ
  have hfin : F n p0 / 3 * ∑ i, ξ i ^ 2 ≤ F n p0 * ‖ξ‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 hα3.le
    linarith
  have hfin2 : F n p0 * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * F n (x, η) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)
  rw [hFξ]
  linarith

end OAI.AnisotropicCalderon.StrictWeightCarleman
