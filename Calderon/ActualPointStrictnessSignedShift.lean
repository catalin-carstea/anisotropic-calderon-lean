import MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.StrictWeightCarleman
theorem exists_signed_shift_of_point_strictness
    (a : Fin 3→Fin 3→R3→ℝ) (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ : R3 → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : R3)
    (hN : 0 < phaseNorm a ϑ p)
    (hstrict : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j p * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) :
    ∃ m : ℝ,
      (∀ xi : Fin 3 → ℝ, xi ≠ 0 → ∑ j, phaseField a ϑ j p*xi j=0 →
        0 < Mgrad a (phaseField a ϑ) p xi+4*m*quad a p xi) ∧
      0 < 2*∑ j,phaseField a ϑ j p*pd j (phaseNorm a ϑ) p-4*m*phaseNorm a ϑ p := by
  set W := phaseField a ϑ with hWdef
  set N := phaseNorm a ϑ with hNdef
  set h : ℝ := (∑ j, W j p * pd j N p) / (2 * N p) with hhdef
  have hW : ∀ j, ContDiff ℝ ∞ (W j) := contDiff_phaseField ha hϑ
  have hNs : ContDiff ℝ ∞ N := contDiff_phaseNorm ha hϑ
  have hac : ∀ i k, Continuous (a i k) := fun i k => (ha i k).continuous
  have hdac : ∀ j i k, Continuous (pd j (a i k)) := fun j i k => (contDiff_pd (ha i k)).continuous
  have hWc : ∀ j, Continuous (W j) := fun j => (hW j).continuous
  have hdWc : ∀ i j, Continuous (pd i (W j)) := fun i j => (contDiff_pd (hW j)).continuous
  have hNc : Continuous N := hNs.continuous
  have hdNc : ∀ j, Continuous (pd j N) := fun j => (contDiff_pd hNs).continuous
                                           
  set Sg : Set (Fin 3 → ℝ) := Metric.sphere 0 1 ∩ {ξ | ∑ j, W j p * ξ j = 0} with hSg
  have hSgc : IsCompact Sg := (isCompact_sphere 0 1).inter_right
    (isClosed_eq (by simp only [Fin.sum_univ_three]; fun_prop) continuous_const)
  have hfc : Continuous (fun ξ : Fin 3 → ℝ => Mgrad a W p ξ + 4 * h * quad a p ξ) := by
    simp only [Mgrad, quad, Fin.sum_univ_three]; fun_prop
  have hqc : Continuous (fun ξ : Fin 3 → ℝ => quad a p ξ) := by
    simp only [quad, Fin.sum_univ_three]; fun_prop
  obtain ⟨μ, hμ, hμf⟩ : ∃ μ : ℝ, 0 < μ ∧ ∀ ξ ∈ Sg, μ ≤ Mgrad a W p ξ + 4 * h * quad a p ξ := by
    rcases Sg.eq_empty_or_nonempty with h0 | hne
    · exact ⟨1, one_pos, by simp [h0]⟩
    obtain ⟨ξ0, hξ0, hmin⟩ := hSgc.exists_isMinOn hne hfc.continuousOn
    refine ⟨_, hstrict ξ0 ?_ hξ0.2, fun ξ hξ => hmin hξ⟩
    intro h0
    have h1 : ‖ξ0‖ = 1 := mem_sphere_zero_iff_norm.mp hξ0.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨B, hB⟩ := hSgc.exists_bound_of_continuousOn hqc.continuousOn
  set Λ : ℝ := max B 1 with hΛ
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛne : Λ ≠ 0 := hΛpos.ne'
  have hc0 : 0 < μ / (2 * Λ) := div_pos hμ (mul_pos two_pos hΛpos)
  set m : ℝ := h - μ / (8 * Λ) with hm
                                                                
  have htanp : ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → ∑ j, W j p * ξ j = 0 →
      0 < Mgrad a W p ξ + 4 * m * quad a p ξ := by
    intro ξ hξ hker
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    set η : Fin 3 → ℝ := ‖ξ‖⁻¹ • ξ with hη
    have hηS : η ∈ Sg := by
      refine ⟨?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
      · show ∑ j, W j p * η j = 0
        rw [hη, lin_smul, hker, mul_zero]
    have h1 := hμf η hηS
    have h2 : quad a p η ≤ Λ := by
      have := hB η hηS
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hη' : 0 < Mgrad a W p η + 4 * m * quad a p η := by
      have e : Mgrad a W p η + 4 * m * quad a p η =
          (Mgrad a W p η + 4 * h * quad a p η) - μ / (2 * Λ) * quad a p η := by
        rw [hm]; ring
      have h3 : μ / (2 * Λ) * quad a p η ≤ μ / (2 * Λ) * Λ :=
        mul_le_mul_of_nonneg_left h2 hc0.le
      have h4 : μ / (2 * Λ) * Λ = μ / 2 := by
        rw [div_mul_eq_mul_div]; exact mul_div_mul_right μ 2 hΛne
      rw [e]; linarith
    have hξη : ξ = ‖ξ‖ • η := by rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hξη, Mgrad_smul, quad_smul]
    have : 0 < ‖ξ‖ ^ 2 := by positivity
    nlinarith
                         
  have hZp : 0 < 2 * ∑ j, W j p * pd j N p - 4 * m * N p := by
    have e : 2 * ∑ j, W j p * pd j N p - 4 * m * N p = μ / (2 * Λ) * N p := by
      have hNne : N p ≠ 0 := hN.ne'
      have hsN : (∑ j, W j p * pd j N p) / (2 * N p) * N p = (∑ j, W j p * pd j N p) / 2 := by
        rw [div_mul_eq_mul_div]; exact mul_div_mul_right _ 2 hNne
      rw [hm, hhdef]
      linear_combination (-4) * hsN
    rw [e]; exact mul_pos hc0 hN
                                             
  exact ⟨m,htanp,hZp⟩

end OAI.AnisotropicCalderon.StrictWeightCarleman
