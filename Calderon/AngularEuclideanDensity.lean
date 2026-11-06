import Calderon.AngularEuclideanGradient
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open MeasureTheory
open scoped InnerProductSpace Gradient ContDiff
namespace OAI.AnisotropicCalderon.AngularPolynomial

lemma directional_fderiv_continuous (u : R3 → ℝ) (hu : ContDiff ℝ ∞ u) (v : R3) :
    Continuous (fun x => fderiv ℝ u x v) := by
  simpa only [inner_gradient_left] using
    ((hu.gradient_right (m := 0) (by simp)).continuous.inner continuous_const :
      Continuous (fun x => ⟪gradient u x, v⟫_ℝ))

lemma compact_scalar_product_integrable (f u v : R3 → ℝ)
    (hf : Continuous f) (hu : Continuous u) (hv : Continuous v)
    (hc : HasCompactSupport u) : Integrable (fun x => f x * (u x * v x)) :=
  (hf.mul (hu.mul hv)).integrable_of_hasCompactSupport (hc.mul_right.mul_left)

lemma compact_directional_cross_term (u a : R3 → ℝ) (hu : ContDiff ℝ ∞ u)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport u) (v : R3) :
    (∫ x : R3, a x * (2 * u x * fderiv ℝ u x v)) =
      -(∫ x : R3, fderiv ℝ a x v * u x ^ 2) := by
  have hu' : Differentiable ℝ u := hu.differentiable (by simp)
  have ha' : Differentiable ℝ a := ha.differentiable (by simp)
  have hd : ∀ x : R3, fderiv ℝ (fun y => u y * u y) x v =
      2 * u x * fderiv ℝ u x v := by
    intro x
    rw [fderiv_fun_mul (hu' x) (hu' x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have h0 := compact_scalar_product_integrable a u u ha.continuous hu.continuous hu.continuous hc
  have h1 := compact_scalar_product_integrable (fun x => fderiv ℝ a x v) u u
    (directional_fderiv_continuous a ha v) hu.continuous hu.continuous hc
  have h2 : Integrable (fun x : R3 => a x * fderiv ℝ (fun y => u y * u y) x v) := by
    simp only [hd]
    convert compact_scalar_product_integrable a u (fun x => 2 * fderiv ℝ u x v)
      ha.continuous hu.continuous
      (continuous_const.mul (directional_fderiv_continuous u hu v)) hc using 1
    funext x
    ring
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure R3)) (f := a) (g := fun x => u x * u x) (v := v)
    h1 h2 h0 (fun x _ => ha' x) (fun x _ => (hu' x).mul (hu' x))
  simpa only [hd, pow_two] using h

/-- Divergence of the actual density times the vector field, in a constant orthonormal basis. -/
def densityWeightedDivergence {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ R3)
    (rho : R3 → ℝ) (A : R3 → R3) (x : R3) : ℝ :=
  ∑ i, fderiv ℝ (fun y => rho y * ⟪A y, b i⟫_ℝ) x (b i)

lemma densityWeightedDivergence_continuous {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (rho : R3 → ℝ) (A : R3 → R3)
    (hr : ContDiff ℝ ∞ rho) (hA : ContDiff ℝ ∞ A) :
    Continuous (densityWeightedDivergence b rho A) := by
  unfold densityWeightedDivergence
  exact continuous_finset_sum _ (fun i _ => directional_fderiv_continuous _
    (hr.mul (hA.inner ℝ contDiff_const)) (b i))

theorem compact_density_gradient_cross_term {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (u rho : R3 → ℝ) (A : R3 → R3)
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ rho) (hA : ContDiff ℝ ∞ A)
    (hc : HasCompactSupport u) :
    (∫ x : R3, rho x * (2 * u x * ⟪gradient u x, A x⟫_ℝ)) =
      -(∫ x : R3, densityWeightedDivergence b rho A x * u x ^ 2) := by
  have hprofile : ∀ i, ContDiff ℝ ∞ (fun x => rho x * ⟪A x, b i⟫_ℝ) :=
    fun i => hr.mul (hA.inner ℝ contDiff_const)
  have hp : ∀ x : R3,
      (∑ i, (rho x * ⟪A x, b i⟫_ℝ) * (2 * u x * fderiv ℝ u x (b i))) =
        rho x * (2 * u x * ⟪gradient u x, A x⟫_ℝ) := by
    intro x
    calc
      _ = ∑ i, (rho x * (2 * u x)) * (⟪A x, b i⟫_ℝ * ⟪b i, gradient u x⟫_ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← inner_gradient_left, real_inner_comm (gradient u x) (b i)]
        ring
      _ = _ := by
        rw [← Finset.mul_sum, b.sum_inner_mul_inner, real_inner_comm (A x) (gradient u x)]
        ring
  have hleft : ∀ i, Integrable (fun x : R3 =>
      (rho x * ⟪A x, b i⟫_ℝ) * (2 * u x * fderiv ℝ u x (b i))) := by
    intro i
    convert compact_scalar_product_integrable _ u (fun x => 2 * fderiv ℝ u x (b i))
      (hprofile i).continuous hu.continuous
      (continuous_const.mul (directional_fderiv_continuous u hu (b i))) hc using 1
    funext x
    ring
  have hright : ∀ i, Integrable (fun x : R3 =>
      fderiv ℝ (fun y => rho y * ⟪A y, b i⟫_ℝ) x (b i) * u x ^ 2) := by
    intro i
    simpa only [Real.norm_eq_abs, sq_abs] using compact_norm_profile_integrable _ u
      (directional_fderiv_continuous _ (hprofile i) (b i)) hu.continuous hc
  calc
    _ = ∫ x : R3, ∑ i, (rho x * ⟪A x, b i⟫_ℝ) *
        (2 * u x * fderiv ℝ u x (b i)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (hp x).symm)
    _ = ∑ i, ∫ x : R3, (rho x * ⟪A x, b i⟫_ℝ) *
        (2 * u x * fderiv ℝ u x (b i)) := integral_finset_sum _ (fun i _ => hleft i)
    _ = ∑ i, -(∫ x : R3, fderiv ℝ (fun y => rho y * ⟪A y, b i⟫_ℝ) x (b i) * u x ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact compact_directional_cross_term u _ hu (hprofile i) hc (b i)
    _ = -(∫ x : R3, densityWeightedDivergence b rho A x * u x ^ 2) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [← integral_finset_sum _ (fun i _ => hright i)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [densityWeightedDivergence, Finset.sum_mul])

theorem compact_density_gradient_square_expansion {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (k : ℝ) (u rho : R3 → ℝ) (A : R3 → R3)
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ rho) (hA : ContDiff ℝ ∞ A)
    (hc : HasCompactSupport u) :
    (∫ x : R3, rho x * ‖gradient u x + (k * u x) • A x‖ ^ 2) =
      (∫ x : R3, rho x * ‖gradient u x‖ ^ 2) +
        k ^ 2 * (∫ x : R3, rho x * ‖A x‖ ^ 2 * u x ^ 2) -
          k * (∫ x : R3, densityWeightedDivergence b rho A x * u x ^ 2) := by
  have hg : Continuous (gradient u) := (hu.gradient_right (m := 0) (by simp)).continuous
  have hgrad := compact_norm_profile_integrable rho (gradient u) hr.continuous hg
    (gradient_hasCompactSupport u hc)
  have hpot : Integrable (fun x : R3 => rho x * ‖A x‖ ^ 2 * u x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using compact_norm_profile_integrable
      (fun x : R3 => rho x * ‖A x‖ ^ 2) u
      (hr.continuous.mul (hA.continuous.norm.pow 2)) hu.continuous hc
  have hcross := compact_scalar_product_integrable rho u
    (fun x => 2 * ⟪gradient u x, A x⟫_ℝ) hr.continuous hu.continuous
    (continuous_const.mul (hg.inner hA.continuous)) hc
  have hcross' : Integrable (fun x : R3 => rho x * (2 * u x * ⟪gradient u x, A x⟫_ℝ)) := by
    convert hcross using 1
    funext x
    ring
  have hp : (fun x : R3 => rho x * ‖gradient u x + (k * u x) • A x‖ ^ 2) =
      fun x => (rho x * ‖gradient u x‖ ^ 2 + k ^ 2 * (rho x * ‖A x‖ ^ 2 * u x ^ 2)) +
        k * (rho x * (2 * u x * ⟪gradient u x, A x⟫_ℝ)) := by
    funext x
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hp, integral_add (f := fun x : R3 => rho x * ‖gradient u x‖ ^ 2 +
      k ^ 2 * (rho x * ‖A x‖ ^ 2 * u x ^ 2))
    (g := fun x : R3 => k * (rho x * (2 * u x * ⟪gradient u x, A x⟫_ℝ)))
    (hgrad.add (hpot.const_mul (k ^ 2))) (hcross'.const_mul k),
    integral_add hgrad (hpot.const_mul (k ^ 2)), integral_const_mul, integral_const_mul,
    compact_density_gradient_cross_term b u rho A hu hr hA hc]
  ring

theorem compact_density_gradient_profile_lower_bound {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ R3) (k c : ℝ) (hk : 0 ≤ k)
    (u rho beta : R3 → ℝ) (A : R3 → R3)
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ rho) (hb : Continuous beta)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport u)
    (hdiv : ∀ x, u x ≠ 0 → densityWeightedDivergence b rho A x ≤ -c * (rho x * beta x)) :
    (∫ x : R3, rho x * ‖gradient u x‖ ^ 2) +
      k ^ 2 * (∫ x : R3, rho x * ‖A x‖ ^ 2 * u x ^ 2) +
        k * c * (∫ x : R3, rho x * beta x * u x ^ 2) ≤
      (∫ x : R3, rho x * ‖gradient u x + (k * u x) • A x‖ ^ 2) := by
  have hi : Integrable (fun x : R3 => densityWeightedDivergence b rho A x * u x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using compact_norm_profile_integrable _ u
      (densityWeightedDivergence_continuous b rho A hr hA) hu.continuous hc
  have hm : Integrable (fun x : R3 => rho x * beta x * u x ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using compact_norm_profile_integrable
      (fun x : R3 => rho x * beta x) u (hr.continuous.mul hb) hu.continuous hc
  have hs := integral_mono hi (hm.const_mul (-c)) (fun x => by
    change densityWeightedDivergence b rho A x * u x ^ 2 ≤
      -c * (rho x * beta x * u x ^ 2)
    by_cases hz : u x = 0
    · simp [hz]
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hdiv x hz) (sq_nonneg (u x)))
  change (∫ x : R3, densityWeightedDivergence b rho A x * u x ^ 2) ≤
    ∫ x : R3, -c * (rho x * beta x * u x ^ 2) at hs
  rw [integral_const_mul] at hs
  have ht := mul_le_mul_of_nonneg_left hs hk
  rw [compact_density_gradient_square_expansion b k u rho A hu hr hA hc]
  nlinarith

end OAI.AnisotropicCalderon.AngularPolynomial
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_directional_cross_term
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_density_gradient_cross_term
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_density_gradient_square_expansion
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.compact_density_gradient_profile_lower_bound
