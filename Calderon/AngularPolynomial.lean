import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
All-degree formal polynomial identities supporting the radial first variation
and the harmonic projection calculation in the original angular argument.
Analytic derivative interpretation and Dirichlet-family estimates remain separate obligations.
-/

noncomputable section

namespace OAI.AnisotropicCalderon.AngularPolynomial

open MvPolynomial

variable {σ : Type*} [Fintype σ]

/-- The Cartesian squared radius in finitely many real variables. -/
def radiusSq : MvPolynomial σ ℝ := ∑ i : σ, X i ^ 2

/-- The formal Cartesian Laplacian of a real multivariate polynomial. -/
def laplacian (q : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, pderiv i (pderiv i q)

lemma pderiv_radiusSq (i : σ) :
    pderiv i (radiusSq : MvPolynomial σ ℝ) = 2 * X i := by
  classical
  simp [radiusSq, Pi.single_apply, mul_ite]

lemma pderiv_pderiv_radiusSq_mul (i : σ) (q : MvPolynomial σ ℝ) :
    pderiv i (pderiv i (radiusSq * q)) =
      2 * q + 4 * (X i * pderiv i q) + radiusSq * pderiv i (pderiv i q) := by
  have htwo : pderiv i (2 : MvPolynomial σ ℝ) = 0 := by
    simpa only [Nat.cast_ofNat] using ((pderiv i).map_natCast 2)
  simp only [pderiv_mul, map_add, pderiv_radiusSq, htwo, pderiv_X_self]
  ring

lemma laplacian_sub (p q : MvPolynomial σ ℝ) :
    laplacian (p - q) = laplacian p - laplacian q := by
  simp [laplacian, map_sub, Finset.sum_sub_distrib]

lemma laplacian_C_mul (c : ℝ) (q : MvPolynomial σ ℝ) :
    laplacian (C c * q) = C c * laplacian q := by
  simp [laplacian, Finset.mul_sum]

/-- The radius-square product rule before homogeneous or harmonic assumptions. -/
lemma laplacian_radiusSq_mul (q : MvPolynomial σ ℝ) :
    laplacian (radiusSq * q) = radiusSq * laplacian q +
      4 * (∑ i : σ, X i * pderiv i q) +
      2 * (Fintype.card σ : MvPolynomial σ ℝ) * q := by
  simp only [laplacian, pderiv_pderiv_radiusSq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Euler's identity converts the cross term into the homogeneous degree. -/
lemma laplacian_radiusSq_mul_of_isHomogeneous {m : ℕ} {q : MvPolynomial σ ℝ}
    (hq : q.IsHomogeneous m) :
    laplacian (radiusSq * q) = radiusSq * laplacian q +
      C (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ)) * q := by
  rw [laplacian_radiusSq_mul, hq.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul, map_add, map_mul, map_ofNat, map_natCast]
  ring

/-- The all-degree identity used for the zero-boundary radial first variation. -/
theorem laplacian_radiusSq_sub_one_mul {m : ℕ} {q : MvPolynomial σ ℝ}
    (hq : q.IsHomogeneous m) (hΔ : laplacian q = 0) :
    laplacian ((radiusSq - 1) * q) =
      C (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ)) * q := by
  rw [sub_mul, one_mul, laplacian_sub, laplacian_radiusSq_mul_of_isHomogeneous hq,
    hΔ, mul_zero, zero_add, sub_zero]

/-- The polynomial solving the first variation with forcing `-q`. -/
def radialFirstVariation (m : ℕ) (q : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  C (-(4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))⁻¹) * ((radiusSq - 1) * q)

theorem laplacian_radialFirstVariation {m : ℕ} {q : MvPolynomial σ ℝ}
    (hq : q.IsHomogeneous m) (hΔ : laplacian q = 0)
    (hc : 4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ) ≠ 0) :
    laplacian (radialFirstVariation m q) = -q := by
  rw [radialFirstVariation, laplacian_C_mul, laplacian_radiusSq_sub_one_mul hq hΔ,
    ← mul_assoc, ← map_mul, neg_mul, inv_mul_cancel₀ hc]
  simp

theorem eval_radialFirstVariation_eq_zero (m : ℕ) (q : MvPolynomial σ ℝ)
    (z : σ → ℝ) (hz : ∑ i : σ, z i ^ 2 = 1) :
    eval z (radialFirstVariation m q) = 0 := by
  simp [radialFirstVariation, radiusSq, hz]

end OAI.AnisotropicCalderon.AngularPolynomial

#print axioms OAI.AnisotropicCalderon.AngularPolynomial.laplacian_radiusSq_sub_one_mul
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.laplacian_radialFirstVariation
#print axioms OAI.AnisotropicCalderon.AngularPolynomial.eval_radialFirstVariation_eq_zero
