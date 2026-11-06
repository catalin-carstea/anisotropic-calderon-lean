import Calderon.MixedKernelConstruction.TaskInterface
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

/-- The degree is selected BEFORE epsilon, with every remaining scalar loss absorbed strictly. -/
theorem exists_native_profile_gain_absorption_parameters
    (c0 c C : ℝ) (hc0 : 0<c0) (hc : 0<c) (hC : 0<C) :
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
      ∃ eps0 : ℝ, 0<eps0 ∧ eps0 ≤ 1 ∧ ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 →
      ∀ beta r q H : ℝ, c0*(p : ℝ) ≤ beta → 0<r → (1/4 : ℝ) ≤ q →
        c*beta*r^2*q^2-C*r^2-C*eps*beta*r^2-C*eps^2*r^2-C*eps*r^2 ≤ H → 0<H := by
  obtain ⟨N,hN⟩ := exists_nat_gt (128*C/(c*c0))
  refine ⟨max 2 N,Nat.le_max_left _ _,?_⟩
  intro p hp
  let eps0 := min 1 (c/(32*C))
  have heps0 : 0<eps0 := lt_min (by norm_num) (div_pos hc (by positivity))
  refine ⟨eps0,heps0,min_le_left _ _,?_⟩
  intro eps heps hepsCap beta r q H hBeta hr hq hLower
  have hpN : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.le_max_right 2 N).trans hp
  have hBetaN : c0*(N : ℝ) ≤ beta := (mul_le_mul_of_nonneg_left hpN hc0.le).trans hBeta
  have hBigN := (div_lt_iff₀ (mul_pos hc hc0)).mp hN
  have hBig : 128*C<c*beta := by
    have hh := mul_le_mul_of_nonneg_left hBetaN hc.le
    nlinarith only [hBigN,hh]
  have hBeta0 : 0 ≤ beta := (mul_nonneg hc0.le (Nat.cast_nonneg p)).trans hBeta
  have heps1 : eps ≤ 1 := hepsCap.trans (min_le_left _ _)
  have hepsDiv : eps ≤ c/(32*C) := hepsCap.trans (min_le_right _ _)
  have hepsBound : C*eps ≤ c/32 := by
    have hh := (le_div_iff₀ (by positivity : 0<32*C)).mp hepsDiv
    nlinarith only [hh]
  have hepsBeta := mul_le_mul_of_nonneg_right hepsBound hBeta0
  have hepsSq : eps^2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ heps (by norm_num : (0 : ℝ) ≤ 1)).mpr heps1
  have hCeps := mul_le_mul_of_nonneg_left heps1 hC.le
  have hCepsSq := mul_le_mul_of_nonneg_left hepsSq hC.le
  have hqSq : (1/16 : ℝ) ≤ q^2 := by nlinarith only [hq,sq_nonneg (q-1/4)]
  have hGain := mul_le_mul_of_nonneg_left hqSq (mul_nonneg hc.le hBeta0)
  have hBracket : 0<c*beta*q^2-C-C*eps*beta-C*eps^2-C*eps := by
    nlinarith only [hBig,hepsBeta,hCeps,hCepsSq,hGain,hC]
  have hPositive := mul_pos (sq_pos_of_pos hr) hBracket
  have hRewrite : r^2*(c*beta*q^2-C-C*eps*beta-C*eps^2-C*eps)=
      c*beta*r^2*q^2-C*r^2-C*eps*beta*r^2-C*eps^2*r^2-C*eps*r^2 := by ring
  rw [hRewrite] at hPositive
  exact hPositive.trans_le hLower

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
