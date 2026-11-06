import Calderon.ProfileHigherJets
import Calderon.DilatedProfileUniform
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.RadiusProfile

lemma norm_iteratedFDeriv_comp_le_of_positive_orders
    (g : ℝ → ℝ) (u : R3 → ℝ) (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (hn : 1 ≤ n) (x : R3) (C D : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g (u x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ u) x‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  let G : ℝ → ℝ := fun s => g s - g (u x)
  have hG : ContDiff ℝ ∞ G := hg.sub contDiff_const
  have hsub (i : ℕ) (hi : 1 ≤ i) :
      iteratedFDeriv ℝ i G (u x) = iteratedFDeriv ℝ i g (u x) := by
    change iteratedFDeriv ℝ i (g - fun _ : ℝ => g (u x)) (u x) = _
    rw [iteratedFDeriv_sub_apply (hg.of_le (by simp)).contDiffAt contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega)]
    simp
  have hGbound : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i G (u x)‖ ≤ C := by
    intro i hi
    by_cases hz : i = 0
    · subst i
      simpa [norm_iteratedFDeriv_zero, G] using hC0
    · rw [hsub i (by omega)]
      exact hC i (by omega) hi
  have h := norm_iteratedFDeriv_comp_le hG hu (by simp) x hGbound hD
  have he : iteratedFDeriv ℝ n (G ∘ u) x = iteratedFDeriv ℝ n (g ∘ u) x := by
    change iteratedFDeriv ℝ n ((g ∘ u) - fun _ : R3 => g (u x)) x = _
    rw [iteratedFDeriv_sub_apply ((hg.comp hu).of_le (by simp)).contDiffAt
      contDiffAt_const, iteratedFDeriv_const_of_ne (by omega)]
    simp only [Pi.zero_apply, sub_zero]
  rwa [he] at h

lemma contDiff_scalar_log_softplus (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun s => Real.log (softplus δ s)) := by
  have he : (fun s => Real.log (softplus δ s)) =
      fun s => Real.log δ + logLogExp (s / δ) :=
    funext (fun s => log_softplus_eq_log_delta_add_logLogExp δ s hδ)
  rw [he]
  exact contDiff_const.add (contDiff_logLogExp.comp (contDiff_id.div_const δ))

def profileJetBoundSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, profileJetBound k

lemma profileJetBoundSum_nonneg (n : ℕ) : 0 ≤ profileJetBoundSum n := by
  exact Finset.sum_nonneg (fun k _ => profileJetBound_nonneg k)

lemma profileJetBound_le_sum (n k : ℕ) (hk : k < n) :
    profileJetBound k ≤ profileJetBoundSum n := by
  exact Finset.single_le_sum (fun i _ => profileJetBound_nonneg i) (Finset.mem_range.mpr hk)

lemma norm_iteratedFDeriv_log_softplus_le (n : ℕ) (hn : 1 ≤ n)
    (δ t : ℝ) (hδ : 0 < δ) :
    ‖iteratedFDeriv ℝ n (fun s => Real.log (softplus δ s)) t‖ ≤
      profileJetBound (n - 1) * logSlope δ t ^ n := by
  have hn' : n - 1 + 1 = n := by omega
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  simpa only [hn'] using abs_iteratedDeriv_log_softplus_le (n - 1) δ t hδ

lemma norm_iteratedFDeriv_log_softplus_comp_le (u : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (x : R3) (B D : ℝ) (hB : 1 ≤ B) (hBa : 1 ≤ B * logSlope δ (u x))
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Real.log (softplus δ (u y))) x‖ ≤
      (n.factorial : ℝ) * profileJetBoundSum n *
        (B * logSlope δ (u x)) ^ n * D ^ n := by
  have ha := (logSlope_pos δ (u x) hδ).le
  have hC : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (fun s => Real.log (softplus δ s)) (u x)‖ ≤
        profileJetBoundSum n * (B * logSlope δ (u x)) ^ n := by
    intro i hi hin
    have hs := norm_iteratedFDeriv_log_softplus_le i hi δ (u x) hδ
    have hterm := profileJetBound_le_sum n (i - 1) (by omega)
    have hp : logSlope δ (u x) ^ i ≤ (B * logSlope δ (u x)) ^ n := by
      have hmul : logSlope δ (u x) ≤ B * logSlope δ (u x) := by nlinarith
      exact (pow_le_pow_left₀ ha hmul i).trans (pow_le_pow_right₀ hBa hin)
    exact hs.trans (mul_le_mul hterm hp (pow_nonneg ha _) (profileJetBoundSum_nonneg n))
  have h := norm_iteratedFDeriv_comp_le_of_positive_orders
    (fun s => Real.log (softplus δ s)) u (contDiff_scalar_log_softplus δ hδ) hu n hn x
    (profileJetBoundSum n * (B * logSlope δ (u x)) ^ n) D (mul_nonneg (profileJetBoundSum_nonneg n) (pow_nonneg (mul_nonneg (by linarith) ha) n)) hC hD
  simpa only [Function.comp_def, mul_assoc] using h

lemma norm_iteratedFDeriv_logProfile_le (u : R3 → ℝ)
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (hn : 1 ≤ n) (δ c : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hp : 1 ≤ p) (x : R3) (B D : ℝ) (hB : 1 ≤ B)
    (hD0 : 0 ≤ D) (hBa : 1 ≤ B * logSlope δ (u x))
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (logProfile δ c p u) x‖ ≤
      (n.factorial : ℝ) * profileJetBoundSum n * (B * D) ^ n *
        ((p : ℝ) * logSlope δ (u x)) ^ n := by
  have hcomp := (contDiff_scalar_log_softplus δ hδ).comp hu
  have hf : iteratedFDeriv ℝ n (logProfile δ c p u) x =
      (p : ℝ) • iteratedFDeriv ℝ n (fun y => Real.log (softplus δ (u y))) x := by
    change iteratedFDeriv ℝ n ((fun _ : R3 => c) +
      fun y => (p : ℝ) * Real.log (softplus δ (u y))) x = _
    rw [iteratedFDeriv_add_apply (f := fun _ : R3 => c)
      (g := fun y => (p : ℝ) * Real.log (softplus δ (u y))) contDiffAt_const
      ((contDiff_const.mul hcomp).of_le (by simp)).contDiffAt,
      iteratedFDeriv_const_of_ne (by omega)]
    simp only [Pi.zero_apply, zero_add]
    simpa only [smul_eq_mul, Function.comp_def] using iteratedFDeriv_const_smul_apply' ((hcomp.of_le (by simp)).contDiffAt) (a := (p : ℝ))
  rw [hf, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg p)]
  have hbase := norm_iteratedFDeriv_log_softplus_comp_le u hu n hn δ hδ x B D hB hBa hD
  have h := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg p)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ n := le_self_pow₀ hpR (by omega)
  have ha := (logSlope_pos δ (u x) hδ).le
  have hr := mul_le_mul_of_nonneg_right hpPow
    (show 0 ≤ (n.factorial : ℝ) * profileJetBoundSum n * (B * logSlope δ (u x)) ^ n * D ^ n by
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (profileJetBoundSum_nonneg n))
        (pow_nonneg (mul_nonneg (by linarith) ha) n)) (pow_nonneg hD0 n))
  convert h.trans hr using 1 <;> simp only [mul_pow] <;> ring

end OAI.AnisotropicCalderon.RadiusProfile

namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile

lemma exists_uniform_depth_jet_bound_on_compact (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (K : Set R3) (hK : IsCompact K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i := by
  let S : R3 → ℝ := fun x => ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i u x‖
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro i hi
    exact (hu.continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max A 1, le_max_right _ _, ?_⟩
  intro i hi hin x hx
  have hsingle : ‖iteratedFDeriv ℝ i u x‖ ≤ S x :=
    by
      change ‖iteratedFDeriv ℝ i u x‖ ≤ ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j u x‖
      exact Finset.single_le_sum (s := Finset.range (n + 1)) (a := i)
        (f := fun j => ‖iteratedFDeriv ℝ j u x‖) (fun j _ => norm_nonneg _)
        (Finset.mem_range.mpr (by omega))
  have hb : S x ≤ A := (le_abs_self _).trans (hA x hx)
  exact hsingle.trans (hb.trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right _ _) (by omega))))

theorem exists_dilated_referenceRadius_fixed_uniform_frechet_jet_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (n : ℕ) (hn : 1 ≤ n) :
    ∃ J : ℝ, 0 < J ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ R : ℝ, 0 < R →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (fun y => Real.log (referenceRadius δ R p L y)) x‖ ≤
          J * metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
            (fun y => Real.log (referenceRadius δ R p L y)) x ^ n := by
  obtain ⟨m, C, T, hm, hC, hbounds⟩ :=
    exists_dilatedReferenceDepth_uniform_metricNorm_bounds g hg L hL K hK
  obtain ⟨D, hD, hjets⟩ := exists_uniform_depth_jet_bound_on_compact
    (referenceDepth L) (contDiff_referenceDepth L) n K hK
  let a0 : ℝ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha0 : 0 < a0 := by
    dsimp [a0]
    exact one_div_pos.mpr (by linarith [log_exp_add_one_pos T])
  let B : ℝ := max 1 (1 / a0)
  have hB : 1 ≤ B := le_max_left _ _
  let A : ℝ := (n.factorial : ℝ) * profileJetBoundSum n * (B * D) ^ n
  have hA : 0 ≤ A := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (profileJetBoundSum_nonneg n))
      (pow_nonneg (mul_nonneg (by linarith) (by linarith)) n)
  refine ⟨A / m ^ n + 1, by positivity, ?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx
  rw [log_referenceRadius δ R p L hδ hR]
  let a : ℝ := logSlope δ (referenceDepth L x)
  let beta : ℝ := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
    (logProfile δ (Real.log R) p (referenceDepth L)) x
  obtain ⟨hmin, hmax, ht⟩ := hbounds lam hlam x hx
  have ha : 0 < a := logSlope_pos δ _ hδ
  have haLower : a0 ≤ a := logSlope_uniform_lower_bound δ _ T hδ hδ1 ht
  have hBa : 1 ≤ B * a := by
    have h1 : 1 / a0 ≤ B := le_max_right _ _
    have h2 := mul_le_mul h1 haLower ha0.le (by positivity : 0 ≤ B)
    have he : (1 / a0) * a0 = 1 := by field_simp
    rwa [he] at h2
  have hbase : ‖iteratedFDeriv ℝ n (logProfile δ (Real.log R) p (referenceDepth L)) x‖ ≤
      A * ((p : ℝ) * a) ^ n :=
    norm_iteratedFDeriv_logProfile_le _ (contDiff_referenceDepth L) n hn δ (Real.log R) p
      hδ hp x B D hB (by linarith) hBa (fun i hi hin => hjets i hi hin x hx)
  have hbetaLower : (p : ℝ) * a * m ≤ beta := by
    dsimp [beta]
    rw [metricDifferentialNorm_logProfile _ δ (Real.log R) p _ x hδ
      ((contDiff_referenceDepth L).differentiable (by simp) x)]
    exact mul_le_mul_of_nonneg_left hmin (mul_nonneg (Nat.cast_nonneg p) ha.le)
  have hbetaNonneg : 0 ≤ beta := Real.sqrt_nonneg _
  have hratio : (p : ℝ) * a ≤ beta / m := (le_div_iff₀ hm).mpr hbetaLower
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg p) ha.le) hratio n
  have hmul := mul_le_mul_of_nonneg_left hpow hA
  have hfinal : A * ((p : ℝ) * a) ^ n ≤ (A / m ^ n) * beta ^ n := by
    simpa only [div_pow, mul_div_assoc, div_mul_eq_mul_div] using hmul
  have hstep : (A / m ^ n) * beta ^ n ≤ (A / m ^ n + 1) * beta ^ n := by
    nlinarith [pow_nonneg hbetaNonneg n]
  exact hbase.trans (hfinal.trans hstep)

end OAI.AnisotropicCalderon.ConformalDepth
