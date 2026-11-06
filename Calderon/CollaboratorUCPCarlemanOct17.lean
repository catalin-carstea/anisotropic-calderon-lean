import Calderon.CollaboratorUniqueContinuationDefinitionOct17
import Calderon.CollaboratorUCPWeightOct17
import Calderon.CollaboratorUCPCompactOct17
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # A local Carleman estimate for `div(A ∇·)`

For smooth symmetric positive definite `A` and a smooth weight `ψ` with nonvanishing gradient on
a closed ball, `φ = exp (λ ψ)` gives, for `λ` large and then `τ` large,
`∫ e^{2τφ} w² ≤ C ∫ e^{2τφ} (div(A∇w))²` for smooth `w` supported in the ball. -/

noncomputable section
open MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon

/-- The Carleman estimate for a fixed weight, given pointwise positivity of the coefficients
of the integration-by-parts integrand on the support. -/
theorem carleman_of_pointwise {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (lam τ κ : ℝ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {K : Set R3} (hK : IsCompact K)
    (hpt : ∀ x ∈ K, ∀ ξ, 0 ≤ Mgrad a (fun j z => τ * Xs a ψ lam j z) x ξ +
      2 * κ * (τ * θs ψ lam x) * quad a x ξ)
    (hz : ∀ x ∈ K, 1 ≤ mzero a (fun j z => τ * Xs a ψ lam j z)
        (fun z => τ ^ 2 * (lam ^ 2 * phi ψ lam z ^ 2 * Nf a ψ z)) x -
      κ * Lop a (fun z => τ * θs ψ lam z) x -
      2 * κ * (τ * θs ψ lam x) * (τ ^ 2 * (lam ^ 2 * phi ψ lam x ^ 2 * Nf a ψ x)) -
      κ * (τ * θs ψ lam x) ^ 2)
    {w : R3 → ℝ} (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ K) :
    (∫ x, Real.exp (2 * τ * phi ψ lam x) * w x ^ 2) ≤
      ∫ x, Real.exp (2 * τ * phi ψ lam x) * Lop a w x ^ 2 := by
  have hφ := contDiff_phi hψ lam
  have hΦ : ContDiff ℝ ∞ (fun z => τ * phi ψ lam z) := by fun_prop
  set v : R3 → ℝ := fun z => Real.exp (τ * phi ψ lam z) * w z with hv_def
  have hv : ContDiff ℝ ∞ v := by fun_prop
  have hwc : HasCompactSupport w := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hws
  have hvc : HasCompactSupport v := hwc.mul_left
  have hvK : tsupport v ⊆ K := (tsupport_mul_subset_right).trans hws
  have hwv : w = fun y => Real.exp (-(τ * phi ψ lam y)) * v y := by
    funext y; simp only [hv_def, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_mul]
  have hconj : ∀ x, Lop a w x = Real.exp (-(τ * phi ψ lam x)) *
      (Sop a (fun z => τ ^ 2 * (lam ^ 2 * phi ψ lam z ^ 2 * Nf a ψ z)) v x +
        Bop (fun j z => τ * Xs a ψ lam j z) v x) := by
    intro x
    rw [hwv, conj_identity ha hsymm hΦ hv x, X_eq ha hψ lam τ, q_eq ha hψ lam τ]
  have hXs : ∀ j, ContDiff ℝ ∞ (fun z => τ * Xs a ψ lam j z) := by
    have := contDiff_bv ha hψ
    intro j; unfold Xs; fun_prop
  have hq : ContDiff ℝ ∞ (fun z => τ ^ 2 * (lam ^ 2 * phi ψ lam z ^ 2 * Nf a ψ z)) := by
    have := contDiff_Nf ha hψ
    fun_prop
  have hθ : ContDiff ℝ ∞ (fun z => τ * θs ψ lam z) := by unfold θs; fun_prop
  obtain ⟨hQi, hQle⟩ := integral_Qfun_le ha hXs hq hθ hv hsymm hvc hκ0 hκ1
  have hvvi : Integrable (fun x => v x * v x) :=
    integrable_of_contDiff_hasCompactSupport (hv.mul hv) (hvc.mul_left)
  calc (∫ x, Real.exp (2 * τ * phi ψ lam x) * w x ^ 2) = ∫ x, v x * v x := by
        congr 1; funext x
        simp only [hv_def]
        rw [show 2 * τ * phi ψ lam x = τ * phi ψ lam x + τ * phi ψ lam x by ring, Real.exp_add]
        ring
    _ ≤ ∫ x, Qfun a (fun j z => τ * Xs a ψ lam j z)
          (fun z => τ ^ 2 * (lam ^ 2 * phi ψ lam z ^ 2 * Nf a ψ z))
          (fun z => τ * θs ψ lam z) κ v x := by
        apply integral_mono hvvi hQi
        intro x
        by_cases hx : x ∈ K
        · have h1 := hpt x hx (grad v x)
          have h2 := mul_le_mul_of_nonneg_right (hz x hx) (mul_self_nonneg (v x))
          simp only [Qfun]
          linarith
        · obtain ⟨h0, h1, -⟩ := vanish_outside (fun h => hx (hvK h))
          have hg : grad v x = 0 := funext h1
          simp [Qfun, hg, h0, Mgrad, quad]
    _ ≤ _ := hQle
    _ = ∫ x, Real.exp (2 * τ * phi ψ lam x) * Lop a w x ^ 2 := by
        congr 1; funext x
        rw [hconj x, mul_pow, ← mul_assoc, sq (Real.exp _), ← Real.exp_add, ← Real.exp_add,
          show 2 * τ * phi ψ lam x + (-(τ * phi ψ lam x) + -(τ * phi ψ lam x)) = 0 by ring,
          Real.exp_zero, one_mul]

theorem carleman {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A)
    (hpos : ∀ x, (A x).PosDef) {ψ : R3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (c : R3) {r : ℝ}
    (hr : 0 < r) (hgrad : ∀ x ∈ closedBall c r, fderiv ℝ ψ x ≠ 0) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ τ₀ C : ℝ, ∀ τ ≥ τ₀, ∀ w : R3 → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ closedBall c r →
      (∫ x, Real.exp (2 * τ * Real.exp (lam * ψ x)) * w x ^ 2) ≤
        C * ∫ x, Real.exp (2 * τ * Real.exp (lam * ψ x)) * divCoeffGrad A w x ^ 2 := by
  classical
  set K := closedBall c r with hK_def
  have hK : IsCompact K := isCompact_closedBall c r
  set a : Fin 3 → Fin 3 → R3 → ℝ := fun i k z => A z i k with ha_def
  have ha : ∀ i k, ContDiff ℝ ∞ (a i k) := fun i k => contDiff_pi.1 (contDiff_pi.1 hA i) k
  have hsymm : ∀ i k, a i k = a k i := fun i k => by
    funext z
    have := (hpos z).1.apply i k
    simpa [ha_def] using this.symm
  have hac : ∀ i k, Continuous (a i k) := fun i k => (ha i k).continuous
  have hquad_pos : ∀ x (ξ : Fin 3 → ℝ), ξ ≠ 0 → 0 < quad a x ξ := fun x ξ hξ => by
    have := (hpos x).dotProduct_mulVec_pos hξ
    convert this using 1
    simp [quad, ha_def, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring
  have hquad_hom : ∀ x (t : ℝ) (ξ : Fin 3 → ℝ), quad a x (t • ξ) = t ^ 2 * quad a x ξ := by
    intro x t ξ; simp [quad, Fin.sum_univ_three]; ring
  obtain ⟨α, hα, hαK⟩ := quad_lower hK (quad a) (by simp only [quad]; fun_prop) hquad_hom
    (fun x _ ξ hξ => hquad_pos x ξ hξ)
  have hbc : ∀ j, ContDiff ℝ ∞ (bv a ψ j) := contDiff_bv ha hψ
  have hE1c : Continuous (fun p : R3 × (Fin 3 → ℝ) => E1 a ψ p.1 p.2) := by
    have : ∀ i j, Continuous (pd i (bv a ψ j)) := fun i j => (contDiff_pd (hbc j)).continuous
    have : ∀ i j k, Continuous (pd j (a i k)) := fun i j k => (contDiff_pd (ha i k)).continuous
    have : ∀ j, Continuous (bv a ψ j) := fun j => (hbc j).continuous
    simp only [E1]; fun_prop
  obtain ⟨C₁, hC₁⟩ := quad_upper hK (E1 a ψ) hE1c (by
    intro x t ξ; simp [E1, Fin.sum_univ_three]; ring)
  have hNc : ContDiff ℝ ∞ (Nf a ψ) := contDiff_Nf ha hψ
  have hNpos : ∀ x ∈ K, 0 < Nf a ψ x := by
    intro x hx
    have hne : grad ψ x ≠ 0 := by
      intro h
      apply hgrad x hx
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
      intro i
      have := congrFun h i
      simpa [grad, pd] using this
    have := hquad_pos x _ hne
    convert this using 1
    simp [Nf_apply, bv_apply, quad, grad, Fin.sum_univ_three]; ring
  obtain ⟨n₀, hn₀, hn₀K⟩ := exists_pos_lower_of_compact hK hNc.continuous.continuousOn hNpos
  obtain ⟨N₁, hN₁⟩ := exists_upper_of_compact hK hNc.continuous.continuousOn
  have hPc : Continuous (Pf a ψ) := by
    have : ∀ j, Continuous (bv a ψ j) := fun j => (hbc j).continuous
    have : ∀ j, Continuous (pd j (Nf a ψ)) := fun j => (contDiff_pd hNc).continuous
    unfold Pf; fun_prop
  obtain ⟨C₂, hC₂⟩ := exists_upper_of_compact hK hPc.continuousOn
  set M := max N₁ 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  set κ := min 1 (n₀ ^ 2 / M) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκN : ∀ x ∈ K, κ * Nf a ψ x ≤ n₀ ^ 2 := by
    intro x hx
    have hN : Nf a ψ x ≤ M := (le_abs_self _).trans ((hN₁ x hx).trans (le_max_left _ _))
    have h1 : κ * Nf a ψ x ≤ n₀ ^ 2 / M * M :=
      mul_le_mul (min_le_right _ _) hN (hNpos x hx).le (by positivity)
    rwa [div_mul_cancel₀ _ (by positivity)] at h1
  set lam := max 1 (max (C₁ / (2 * κ * α)) ((C₂ + n₀ ^ 2) / n₀ ^ 2)) with hlam
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hlamC₁ : C₁ ≤ 2 * κ * lam * α := by
    have h : C₁ / (2 * κ * α) ≤ lam := (le_max_left _ _).trans (le_max_right _ _)
    have := (div_le_iff₀ (by positivity)).1 h
    linarith
  have hlamC₂ : (C₂ + n₀ ^ 2) / n₀ ^ 2 ≤ lam := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨lam, by linarith, ?_⟩
  have hφc := contDiff_phi hψ lam
  obtain ⟨φ₀, hφ₀, hφ₀K⟩ := exists_pos_lower_of_compact hK hφc.continuous.continuousOn
    (fun x _ => Real.exp_pos _)
  obtain ⟨φ₁, hφ₁⟩ := exists_upper_of_compact hK hφc.continuous.continuousOn
  have hRc : Continuous (Rf a ψ lam κ) := by
    have hXs : ∀ j, ContDiff ℝ ∞ (Xs a ψ lam j) := by
      intro j; unfold Xs; fun_prop
    have h1 := contDiff_Lop ha (contDiff_divV hXs)
    have hθs : ContDiff ℝ ∞ (θs ψ lam) := by unfold θs; fun_prop
    have h2 := contDiff_Lop ha hθs
    unfold Rf; exact (h1.add (contDiff_const.mul h2)).continuous
  obtain ⟨D, hD⟩ := exists_upper_of_compact hK hRc.continuousOn
  refine ⟨max 1 ((κ * lam ^ 4 * φ₁ ^ 2 + |D| + 1) / (2 * n₀ ^ 2 * lam ^ 3 * φ₀ ^ 3)), 1, ?_⟩
  intro τ hτ w hw hws
  have hτ1 : 1 ≤ τ := (le_max_left _ _).trans hτ
  have hτ' : κ * lam ^ 4 * φ₁ ^ 2 + |D| + 1 ≤ τ * (2 * n₀ ^ 2 * lam ^ 3 * φ₀ ^ 3) := by
    have h := (le_max_right _ _).trans hτ
    have := (div_le_iff₀ (by positivity)).1 h
    linarith
  have key := carleman_of_pointwise ha hsymm hψ lam τ κ hκ0.le hκ1 hK
    (fun x hx ξ => by
      rw [grad_coeff ha hsymm hψ lam τ κ x ξ]
      exact grad_part_nonneg (by linarith) (by linarith) (Real.exp_pos _).le (hC₁ x hx ξ)
        (hαK x hx ξ) hκ0.le hlamC₁ (by positivity))
    (fun x hx => by
      rw [zero_coeff ha hψ lam τ κ x]
      exact zero_part_ge_one hn₀
        (B_ge hn₀ (hn₀K x hx) (hκN x hx) (hC₂ x hx) hlamC₂ (by linarith))
        hlam1 hφ₀ (hφ₀K x hx) ((le_abs_self _).trans (hφ₁ x hx)) hκ0.le
        ((le_abs_self _).trans ((hD x hx).trans (le_abs_self _))) (abs_nonneg _) hτ1 hτ')
    hw hws
  simpa [phi, divCoeffGrad, Lop, pd, ha_def] using key

end OAI.AnisotropicCalderon
