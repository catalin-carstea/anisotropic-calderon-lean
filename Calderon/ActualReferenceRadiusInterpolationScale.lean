import Calderon.ReferenceRadiusScaling
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ConformalDepth
open RadiusProfile

/-- For the manuscript's three-dimensional interpolation exponent 1/23,
the true softplus radius root dominates the interpolation ball scale at
all sufficiently small radii, uniformly in the shrinkage parameter. -/
theorem exists_referenceRadius_interpolationScale_smallness
    (L R C : ℝ) (p : ℕ) (hR : 0 < R) (hC : 0 < C) (hp : 24 ≤ p) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ δ : ℝ, 0 < δ → ∀ y : R3,
      referenceRadius δ R p L y < rho →
        C * (referenceRadius δ R p L y) ^ ((1 : ℝ) / 23) ≤
          (1/2 : ℝ) * softplus δ (referenceDepth L y) := by
  let A : ℝ := (2 * C)^23 * R
  have hA : 0 < A := mul_pos (pow_pos (by positivity : 0 < 2 * C) _) hR
  let u0 : ℝ := 1 / (1 + A)
  have hu0 : 0 < u0 := by dsimp [u0]; positivity
  have hu0one : u0 ≤ 1 := by
    dsimp [u0]
    apply (div_le_iff₀ (by positivity : 0 < 1 + A)).2
    linarith
  have hAu0 : A * u0 ≤ 1 := by
    dsimp [u0]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 1 + A)).2
    linarith
  let rho : ℝ := R * u0^p
  have hrho : 0 < rho := mul_pos hR (pow_pos hu0 _)
  refine ⟨rho,hrho,?_⟩
  intro δ hδ y hrsmall
  let u : ℝ := softplus δ (referenceDepth L y)
  let r : ℝ := referenceRadius δ R p L y
  have hu : 0 < u := softplus_pos δ _ hδ
  have hr : 0 < r := referenceRadius_pos δ R p L y hδ hR
  have hrEq : r = R * u^p := rfl
  have huPow : u^p < u0^p := by
    have h : r < rho := hrsmall
    rw [hrEq] at h
    dsimp [rho] at h
    exact lt_of_mul_lt_mul_left h hR.le
  have huSmall : u < u0 := lt_of_pow_lt_pow_left₀ p hu0.le huPow
  have huOne : u ≤ 1 := huSmall.le.trans hu0one
  have huPow24 : u^p ≤ u^24 := pow_le_pow_of_le_one hu.le huOne hp
  have hAu : A * u ≤ 1 := (mul_le_mul_of_nonneg_left huSmall.le hA.le).trans hAu0
  have hPower : A * u^p ≤ u^23 := by
    calc
      A * u^p ≤ A * u^24 := mul_le_mul_of_nonneg_left huPow24 hA.le
      _ = (u^23) * (A * u) := by ring
      _ ≤ u^23 * 1 := mul_le_mul_of_nonneg_left hAu (pow_nonneg hu.le _)
      _ = u^23 := mul_one _
  have hRoot : ((r ^ ((1 : ℝ) / 23)) ^ 23) = r := by
    convert Real.rpow_inv_natCast_pow hr.le (by norm_num : (23 : ℕ) ≠ 0) using 1 <;> norm_num
  have hPow : (2 * C * (r ^ ((1 : ℝ) / 23)))^23 ≤ u^23 := by
    rw [mul_pow, hRoot]
    convert hPower using 1 <;> simp only [A, hrEq] <;> ring
  have hLeftNonneg : 0 ≤ 2 * C * (r ^ ((1 : ℝ) / 23)) := by positivity
  have hBase : 2 * C * (r ^ ((1 : ℝ) / 23)) ≤ u :=
    le_of_pow_le_pow_left₀ (by norm_num : (23 : ℕ) ≠ 0) hu.le hPow
  nlinarith [Real.rpow_nonneg hr.le ((1 : ℝ) / 23)]

end OAI.AnisotropicCalderon.ConformalDepth
