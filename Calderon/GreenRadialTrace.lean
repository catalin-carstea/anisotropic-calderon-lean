import Calderon.HarmonicRaising
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

noncomputable section
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open MvPolynomial
open OAI.AnisotropicCalderon.AngularPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The actual continuous linear derivative of polynomial evaluation. -/
def polynomialFDeriv (p : MvPolynomial σ ℝ) (z : σ → ℝ) : (σ → ℝ) →L[ℝ] ℝ :=
  ∑ i : σ, (ContinuousLinearMap.proj i).smulRight (eval z (pderiv i p))

lemma polynomialFDeriv_apply (p : MvPolynomial σ ℝ) (z v : σ → ℝ) :
    polynomialFDeriv p z v = ∑ i : σ, v i * eval z (pderiv i p) := by
  simp [polynomialFDeriv, smul_eq_mul]

lemma polynomialFDeriv_C (c : ℝ) (z : σ → ℝ) :
    polynomialFDeriv (C c) z = 0 := by
  simp [polynomialFDeriv]

lemma polynomialFDeriv_add (p q : MvPolynomial σ ℝ) (z : σ → ℝ) :
    polynomialFDeriv (p + q) z = polynomialFDeriv p z + polynomialFDeriv q z := by
  ext v
  simp [polynomialFDeriv_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma polynomialFDeriv_mul (p q : MvPolynomial σ ℝ) (z : σ → ℝ) :
    polynomialFDeriv (p * q) z =
      eval z p • polynomialFDeriv q z + eval z q • polynomialFDeriv p z := by
  ext v
  simp only [polynomialFDeriv_apply, add_apply,
    smul_apply, smul_eq_mul, pderiv_mul, map_add, map_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma polynomialFDeriv_X (j : σ) (z : σ → ℝ) :
    polynomialFDeriv (X j) z = ContinuousLinearMap.proj j := by
  classical
  ext v
  simp [polynomialFDeriv_apply, pderiv_X, Pi.single_apply, mul_ite]

/-- This connects the previously formal polynomial derivatives to genuine analysis. -/
theorem hasFDerivAt_eval (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    HasFDerivAt (fun x : σ → ℝ => eval x p) (polynomialFDeriv p z) z := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [polynomialFDeriv_C]
    simpa only [eval_C] using hasFDerivAt_const (𝕜 := ℝ) c z
  | add p q hp hq =>
    rw [polynomialFDeriv_add]
    convert! hp.add hq using 1 <;> ext x <;> simp
  | mul_X p j hp =>
    rw [polynomialFDeriv_mul, polynomialFDeriv_X, eval_X]
    convert! hp.mul (hasFDerivAt_apply j z) using 1 <;> ext x <;> simp

lemma fderiv_eval_apply (p : MvPolynomial σ ℝ) (z v : σ → ℝ) :
    fderiv ℝ (fun x : σ → ℝ => eval x p) z v =
      ∑ i : σ, v i * eval z (pderiv i p) := by
  rw [(hasFDerivAt_eval p z).fderiv, polynomialFDeriv_apply]

lemma fderiv_eval_coordinate (p : MvPolynomial σ ℝ) (z : σ → ℝ) (i : σ) :
    fderiv ℝ (fun x : σ → ℝ => eval x p) z (Pi.single i 1) =
      eval z (pderiv i p) := by
  classical
  simp [fderiv_eval_apply, Pi.single_apply, ite_mul]

/-- Cartesian Laplacian using actual twice-applied Fréchet derivatives. -/
def cartesianLaplacian (u : (σ → ℝ) → ℝ) (z : σ → ℝ) : ℝ :=
  ∑ i : σ, fderiv ℝ (fun x => fderiv ℝ u x (Pi.single i 1)) z (Pi.single i 1)

theorem cartesianLaplacian_eval (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    cartesianLaplacian (fun x => eval x p) z = eval z (laplacian p) := by
  classical
  simp only [cartesianLaplacian, fderiv_eval_coordinate, laplacian, map_sum]

/-- The polynomial directional derivative for the actual center drift. -/
def driftDerivative (b : σ → ℝ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, C (b i) * pderiv i p

lemma driftDerivative_isHomogeneous {k : ℕ} {p : MvPolynomial σ ℝ}
    (hp : p.IsHomogeneous k) (b : σ → ℝ) :
    (driftDerivative b p).IsHomogeneous (k - 1) := by
  exact IsHomogeneous.sum _ _ _ fun i _ => hp.pderiv.C_mul _

lemma laplacian_driftDerivative (b : σ → ℝ) (p : MvPolynomial σ ℝ)
    (hp : laplacian p = 0) : laplacian (driftDerivative b p) = 0 := by
  simp [driftDerivative, laplacian_sum, laplacian_C_mul, laplacian_pderiv, hp]

/-- The zero boundary solution of the radial first variation, with genuine drift forcing. -/
def driftFirstVariation (k : ℕ) (b : σ → ℝ) (p : MvPolynomial σ ℝ) :=
  radialFirstVariation (k - 1) (driftDerivative b p)

theorem cartesianLaplacian_driftFirstVariation [Nonempty σ] {k : ℕ}
    {p : MvPolynomial σ ℝ} (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0)
    (b z : σ → ℝ) :
    cartesianLaplacian (fun x => eval x (driftFirstVariation k b p)) z =
      -fderiv ℝ (fun x => eval x p) z b := by
  rw [cartesianLaplacian_eval, driftFirstVariation,
    laplacian_radialFirstVariation (driftDerivative_isHomogeneous hp b)
      (laplacian_driftDerivative b p hΔ)
      (ne_of_gt (radiusSq_laplacian_coefficient_pos (k - 1)))]
  simp [driftDerivative, fderiv_eval_apply]

theorem eval_driftFirstVariation_eq_zero (k : ℕ) (b : σ → ℝ)
    (p : MvPolynomial σ ℝ) (z : σ → ℝ) (hz : ∑ i : σ, z i ^ 2 = 1) :
    eval z (driftFirstVariation k b p) = 0 :=
  eval_radialFirstVariation_eq_zero _ _ z hz

/-- Exact outward radial derivative of the explicit zero-boundary solution. -/
theorem fderiv_radialFirstVariation_at_sphere (m : ℕ) (q : MvPolynomial σ ℝ)
    (z : σ → ℝ) (hz : ∑ i : σ, z i ^ 2 = 1) :
    fderiv ℝ (fun x => eval x (radialFirstVariation m q)) z z =
      (-2 / (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))) * eval z q := by
  have hr : eval z (radiusSq : MvPolynomial σ ℝ) = 1 := by
    simp [radiusSq, hz]
  have hpartial (i : σ) : eval z (pderiv i (radialFirstVariation m q)) =
      -(4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))⁻¹ * (2 * z i * eval z q) := by
    rw [radialFirstVariation]
    simp only [pderiv_mul, pderiv_C, zero_mul, zero_add, map_sub, pderiv_one,
      sub_zero, pderiv_radiusSq, map_mul, map_add, map_sub, map_ofNat, map_one,
      eval_C, eval_X, hr, sub_self, zero_mul, add_zero]
  rw [fderiv_eval_apply]
  simp_rw [hpartial]
  calc
    _ = (-2 / (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))) * eval z q *
        ∑ i : σ, z i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hz, mul_one]

/-- The actual trace identity in the selected dimension three. -/
theorem fderiv_driftFirstVariation_three_at_sphere {k : ℕ} (hk : 1 ≤ k)
    (b : Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ)
    (hz : ∑ i : Fin 3, z i ^ 2 = 1) :
    fderiv ℝ (fun x => eval x (driftFirstVariation k b p)) z z =
      -(2 * (k : ℝ) + 1)⁻¹ * fderiv ℝ (fun x => eval x p) z b := by
  rw [driftFirstVariation, fderiv_radialFirstVariation_at_sphere _ _ z hz]
  have hc : -2 / (4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card (Fin 3) : ℝ)) =
      -(2 * (k : ℝ) + 1)⁻¹ := by
    rw [Nat.cast_sub hk]
    norm_num only [Fintype.card_fin, Nat.cast_ofNat, Nat.cast_one]
    have hden : 4 * ((k : ℝ) - 1) + 6 = 2 * (2 * (k : ℝ) + 1) := by ring
    rw [hden]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  rw [hc]
  simp [driftDerivative, fderiv_eval_apply]

lemma driftDerivative_C (b : σ → ℝ) (c : ℝ) : driftDerivative b (C c) = 0 := by
  simp [driftDerivative]

lemma driftFirstVariation_C (k : ℕ) (b : σ → ℝ) (c : ℝ) :
    driftFirstVariation k b (C c) = 0 := by
  simp [driftFirstVariation, driftDerivative_C, radialFirstVariation]

lemma driftDerivative_X (b : σ → ℝ) (j : σ) : driftDerivative b (X j) = C (b j) := by
  classical
  simp [driftDerivative, pderiv_X, Pi.single_apply, mul_ite]

theorem fderiv_driftFirstVariation_three_degree_one (b z : Fin 3 → ℝ)
    (j : Fin 3) (hz : ∑ i : Fin 3, z i ^ 2 = 1) :
    fderiv ℝ (fun x => eval x (driftFirstVariation 1 b (X j))) z z = -(b j) / 3 := by
  rw [fderiv_driftFirstVariation_three_at_sphere (by omega) b (X j) z hz]
  rw [(hasFDerivAt_eval (X j) z).fderiv, polynomialFDeriv_X]
  simp [div_eq_mul_inv]
  ring

end OAI.AnisotropicCalderon.GreenRadialTrace

#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.hasFDerivAt_eval
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.cartesianLaplacian_driftFirstVariation
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.eval_driftFirstVariation_eq_zero
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.fderiv_driftFirstVariation_three_at_sphere
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.fderiv_driftFirstVariation_three_degree_one

